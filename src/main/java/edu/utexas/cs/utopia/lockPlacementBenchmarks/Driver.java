package edu.utexas.cs.utopia.lockPlacementBenchmarks;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.microsoft.z3.Context;

import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.LockConstraintProblem;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.PessimisticPointerAnalysis;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis.MonitorAnalysis;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.instrumentation.AtomicSegmentMarker;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.instrumentation.ClinitGuarantor;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.instrumentation.LockInserter;
import soot.Modifier;
import soot.NullType;
import soot.Pack;
import soot.PackManager;
import soot.Printer;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.SourceLocator;
import soot.Transform;
import soot.jimple.JasminClass;
import soot.jimple.Jimple;
import soot.options.Options;
import soot.util.JasminOutputStream;

/**
 * Based on edu.utexas.cs.utopia.cfpchecker.Driver by kferles
 * 
 * Command line interface:
 * 
 * java -jar lockPlacementBenchmarks.jar appClass -- <soot_arg1> ... <soot_argn>
 */
public class Driver
{
	private static Logger log = LoggerFactory.getLogger(Driver.class);
	private static HashSet<SootClass> classesToWrite = new HashSet<>();
	
	/**
	 * Get index before first soot argument
	 * 
	 * @param args command line args
	 * @return First index where "--" appears, or -1
	 */
    private static int argsSplitIndex(String[] args)
    {
        for (int i = 0; i < args.length; ++i)
            if (args[i].equals("--"))
                return i;
        return -1;
    }

    /**
     * Run soot packages using soot command line args,
     * then do our transforms
     * 
     * @param args 
     */
    public static void main(String[] args)
    {
    	// Parse command line arguments
    	int splitIndex = argsSplitIndex(args);
        String[] sootOptions, checkerOptions;

        CmdLine cmdLine = new CmdLine();

        if (splitIndex == -1)
        {
            checkerOptions = args;
            sootOptions = new String[]{};
        }
        else
        {
            checkerOptions = Arrays.copyOfRange(args, 0, splitIndex);
            sootOptions = Arrays.copyOfRange(args, splitIndex + 1, args.length);
        }

        PackManager packManager = PackManager.v();
        Options sootCmdLine = Options.v();

    	log.debug("Parsing soot command line arguments");
        sootCmdLine.parse(sootOptions);
        // From edu.utexas.cs.utopia.expresso.Driver
        int cmdLineOutFormat = sootCmdLine.output_format();
        if (cmdLineOutFormat != Options.output_format_jimple)
        {
            if (cmdLineOutFormat != Options.output_format_class)
            {
                System.err.println("Unsupported output format. Supported formats are jimple (-f jimple) and bytecode (default format)");
                System.exit(1);
            }
            sootCmdLine.set_output_format(Options.output_format_jimple);
        }

        //sootCmdLine.set_ignore_resolution_errors(true);
        
        // Parse non-soot args
        log.debug("Parsing non-soot command line arguments");
        String err = cmdLine.parseArgs(checkerOptions);

        if (err != null || cmdLine.isHelp())
        {
            if (err != null)
                System.err.println(err);

            System.err.println(cmdLine.usage());
            System.exit(1);
        }

        // Do not convert code to BAF
        sootCmdLine.set_output_format(Options.output_format_jimple);
        
        // Load relevant classes, set class in monitor file as applications
        log.debug("adding/loading classes to soot");
        // We will need to add lock managers to implement nested atomic segments
        //
        // We are loading at the BODIES level because we may need to modify
        // classes to insert locks...
        Scene.v().addBasicClass("edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.TwoPhaseLockManager",
        					SootClass.BODIES);
        // We need these because we're working with explicit monitors
        Scene.v().addBasicClass("java.util.concurrent.locks.ReentrantLock", SootClass.BODIES);
        Scene.v().addBasicClass("java.util.concurrent.locks.Condition", SootClass.BODIES);
        // Now load application classes from the command line
        for(String className : cmdLine.getTargetClasses()) {
        	SootClass targetClass = Scene.v().loadClass(className, SootClass.BODIES);
        	targetClass.setApplicationClass();
        }
        Scene.v().loadNecessaryClasses();

        // run packs
        log.info("Running command-line specified soot packs");
        packManager.runPacks();

        Instant start = Instant.now();
        
        // TODO : make this a command line option, actually do an analysis
        // Get pointer analysis
        //PointerAnalysis ptrAnalysis = new OptimisticPointerAnalysis();
        PessimisticPointerAnalysis ptrAnalysis = new PessimisticPointerAnalysis();
        int localCost = cmdLine.getLocalCost(),
        	globalCost = cmdLine.getGlobalCost();
        boolean logZ3 = cmdLine.getDebugZ3();
        
        log.info("Performing analyses");
        List<MonitorAnalysis> monitorAnalyses = new ArrayList<>();
        List<LockConstraintProblem> lockProblems = new ArrayList<>();
        for(String className : cmdLine.getTargetClasses()) {
        	SootClass targetClass = Scene.v().getSootClass(className);
        	MonitorAnalysis mtrAnalysis = new MonitorAnalysis(targetClass, ptrAnalysis);
        	Context ctx = new Context();
        	LockConstraintProblem lockPrb = new LockConstraintProblem(ctx, mtrAnalysis, localCost, globalCost, logZ3);
        	monitorAnalyses.add(mtrAnalysis);
        	lockProblems.add(lockPrb);
        }
        
        // Add and apply our transformers!
        Pack jtpPack = packManager.getPack("jtp");     
        
        log.info("Applying custom transforms");
        ClinitGuarantor clinitGtr = new ClinitGuarantor();
        for(int i = 0; i < cmdLine.getTargetClasses().size(); ++i) {
        	String className = cmdLine.getTargetClasses().get(i);
        	SootClass targetClass = Scene.v().getSootClass(className);
        	
        	// get our analysis
        	MonitorAnalysis mtrAnalysis = monitorAnalyses.get(i);
        	LockConstraintProblem lockProb = lockProblems.get(i);
        	
        	// make sure we have a clinit
        	clinitGtr.guaranteeClinitExists(targetClass);
        	
            // Mark the atomic segments
        	log.debug("Marking atomic segments");
            AtomicSegmentMarker atomicExtractor = new AtomicSegmentMarker(mtrAnalysis.getAtomicSegments());
            Transform atomicExtractorT = new Transform("jtp.atomicSegmentMarker." + className,
            										   atomicExtractor);
            jtpPack.add(atomicExtractorT);
        	
        	
        	log.debug("Inserting locks!");
            LockInserter lockInsert = new LockInserter(lockProb.getLockAssignment(),
            										   lockProb.getAssignedToGlobal(),
            										   mtrAnalysis);
            Transform lockInsertT = new Transform("jtp.lockInsertion." + targetClass.getName(),
            									  lockInsert);
            jtpPack.add(lockInsertT);
            for(SootMethod targetMethod : targetClass.getMethods()) {
        		lockInsertT.apply(targetMethod.getActiveBody());
        	}
            Driver.addClassToWrite(targetClass);
        }
        
        // Print classes out to file
        // Based on edu.utexas.cs.utopia.expresso.Driver
        log.debug("Writing transformed classes to files");
        for(SootClass targetClass : classesToWrite) {
	        if (cmdLineOutFormat == Options.output_format_class)
	        {
	            String fileName = SourceLocator.v().getFileNameFor(targetClass, Options.output_format_class);
	
	            try (PrintWriter writerOut = new PrintWriter(new OutputStreamWriter(new JasminOutputStream(new FileOutputStream(fileName)))))
	            {
	                JasminClass jasminClass = new soot.jimple.JasminClass(targetClass);
	                jasminClass.print(writerOut);
	                writerOut.flush();
	            }
	            catch (FileNotFoundException e)
	            {
	                System.err.println(e.getMessage());
	                System.exit(1);
	            }
	        }
	        else
	        {
	            String fileName = SourceLocator.v().getFileNameFor(targetClass, Options.output_format_jimple);
	            try (PrintWriter writerOut = new PrintWriter(new OutputStreamWriter(new FileOutputStream(fileName))))
	            {
	                Printer.v().printTo(targetClass, writerOut);
	            }
	            catch (FileNotFoundException e)
	            {
	                System.err.println(e.getMessage());
	                System.exit(1);
	            }
	        }
        }
        
        Instant end = Instant.now();
        System.out.println("Total exec: " + Duration.between(start, end));
    }
    
    /**
     * If we modified cls, we will want to write it out
     * @param cls
     */
    public static void addClassToWrite(SootClass cls) {
    	classesToWrite.add(cls);
    }
}