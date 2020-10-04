package edu.utexas.cs.utopia.lockPlacementBenchmarks;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.time.Duration;
import java.time.Instant;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.microsoft.z3.Context;

import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.AccessedBeforeRelation;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.AtomicSegmentMarker;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.LockConstraintProblem;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.LockInserter;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.OptimisticPointerAnalysis;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.OutOfScopeCalculator;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.PointerAnalysis;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.SharedLValuesExtractor;
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
        PointerAnalysis ptrAnalysis = new OptimisticPointerAnalysis();
        // TODO : make these command line settings, with this default
        int localCost = 1, globalCost = 2;
        // TODO : make these command line settings
        boolean logZ3 = true;
        
        // Adding our transformers!
        Pack jtpPack = packManager.getPack("jtp");     
        log.debug("Adding custom soot transforms");
   
        // Used to get the atomic segments
        AtomicSegmentMarker atomicExtractor = new AtomicSegmentMarker();
        Transform atomicExtractorT = new Transform("jtp.atomicSegmentMarker",
        										   atomicExtractor);
        jtpPack.add(atomicExtractorT);
        
        log.info("Applying custom transforms");
        for(String className : cmdLine.getTargetClasses()) {
        	SootClass targetClass = Scene.v().getSootClass(className);
        	
        	// Clear previous atomic segments
        	atomicExtractor.getAtomicSegments().clear();
        	
        	// make sure targetClass has a clinit method
        	// https://ptolemy.berkeley.edu/ptolemyII/ptII10.0/ptII10.0.1/ptolemy/copernicus/kernel/SootUtilities.java
        	if(!targetClass.declaresMethodByName("<clinit>")) {
        		@SuppressWarnings("rawtypes")
				SootMethod emptyClinit = new SootMethod("<clinit>",
		        										new LinkedList(),
		        										NullType.v(),
		        										Modifier.PUBLIC);
        		emptyClinit.setActiveBody(Jimple.v().newBody(emptyClinit));
        		targetClass.addMethod(emptyClinit);
        	}
            // Extract atomic segments from methods
        	log.debug("Extracting atomic segments from " + className);
        	for(SootMethod targetMethod : targetClass.getMethods()) {
        		atomicExtractorT.apply(targetMethod.getActiveBody());
        	}
        	
        	// Now get the shared lvalues
        	log.debug("Extracting shared LValues from " + className);
        	SharedLValuesExtractor lValueExtractor = 
                new SharedLValuesExtractor(atomicExtractor.getAtomicSegments());
        	
        	// Now get the scope
        	log.debug("Determining scope of shared LValues for each atomic segment");
        	OutOfScopeCalculator scopeCalc = 
        		new OutOfScopeCalculator(atomicExtractor.getAtomicSegments(),
        								 lValueExtractor.getSharedLValues());

        	// Compute the accessed-before relation 
        	log.debug("extracting accessed before relation");
        	AccessedBeforeRelation 
        		accBefore = new AccessedBeforeRelation(ptrAnalysis,
        											   targetClass,
        											   lValueExtractor.getSharedLValues());
        	
        	// Build and solve our constraints
        	log.debug("Building and solving lock constraint problem");
        	LockConstraintProblem 
        		lockProblem = new LockConstraintProblem(new Context(),
									  					lValueExtractor.getSharedLValues(),
														lValueExtractor.getLValuesAccessedIn(),
														scopeCalc.getOutOfScope(),
														accBefore.getTopoAccessedBefore(),
														ptrAnalysis,
														localCost,
														globalCost,
														logZ3);
        	
        	 // Used to insert locks
        	log.debug("Inserting locks!");
            LockInserter lockInsert = new LockInserter(lockProblem.getLockAssignment(),
            										   atomicExtractor.getAtomicSegments(),
            										   lValueExtractor.getLValuesAccessedIn(),
            										   accBefore.getTopoAccessedBefore());
            Transform lockInsertT = new Transform("jtp.lockInsertion" + targetClass.getName(),
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