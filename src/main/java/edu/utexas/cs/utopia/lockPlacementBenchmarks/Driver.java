package edu.utexas.cs.utopia.lockPlacementBenchmarks;

import soot.Pack;
import soot.PackManager;
import soot.Printer;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.SourceLocator;
import soot.Transform;
import soot.jimple.JasminClass;
import soot.options.Options;
import soot.util.JasminOutputStream;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.time.Duration;
import java.time.Instant;
import java.util.Arrays;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.AtomicSegmentExtractor;

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
        Scene.v().addBasicClass("edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.TwoPhaseLockManager",
        					SootClass.SIGNATURES);
        // We need these because we're working with explicit monitors
        Scene.v().addBasicClass("java.util.concurrent.locks.ReentrantLock", SootClass.SIGNATURES);
        Scene.v().addBasicClass("java.util.concurrent.locks.Condition", SootClass.SIGNATURES);
        // Now load application classes from the command line
        for(String className : cmdLine.getTargetClasses()) {
        	SootClass targetClass = Scene.v().loadClass(className, SootClass.SIGNATURES);
        	targetClass.setApplicationClass();
        }
        Scene.v().loadNecessaryClasses();

        // run packs
        log.info("Running command-line specified soot packs");
        packManager.runPacks();

        Instant start = Instant.now();
        
        // Adding our transformers!
        Pack jtpPack = packManager.getPack("jtp");
        
        log.debug("Adding custom soot transforms");
        AtomicSegmentExtractor atomicExtractor = new AtomicSegmentExtractor();
        Transform atomicExtractorT = new Transform("jtp.ase", atomicExtractor);
        jtpPack.add(atomicExtractorT);
        
        log.info("Applying custom transforms");
        // Extract atomic segments from all application methods
        for(String className : cmdLine.getTargetClasses()) {
        	SootClass targetClass = Scene.v().getSootClass(className);
        	for(SootMethod targetMethod : targetClass.getMethods()) {
        		atomicExtractorT.apply(targetMethod.getActiveBody());
        	}
        }

        /**
        // Adding our transformers!
        Pack wjtpPack = packManager.getPack("wjtp");

        ImmediateRecursionEliminator recursionEliminator = new ImmediateRecursionEliminator(spec);
        APICallRewriter apiCallRewriter = new APICallRewriter(spec);
        WildcardTransformation wildcardTransformation = new WildcardTransformation(spec);
        Map<Unit, APISpecCall> invToSpecCalls = wildcardTransformation.getInvokeStmtToSpecCalls();
        StaticLocalizeTransformation localizeTransform = new StaticLocalizeTransformation(spec);
        TransitiveReadWriteSetGenerator writeSetGenerator = TransitiveReadWriteSetGenerator.v(spec);

        NormalizeBlocks normBBs = new NormalizeBlocks(spec);
        NormalizeReturnStmts normRet = new NormalizeReturnStmts(spec);
        SwitchStatementRemover swRemover = new SwitchStatementRemover(spec);
        Assumify assumify = new Assumify(spec);
        Devirtualize devirt = new Devirtualize(spec);
        BreakBlocksOnCalls breakBlocks = new BreakBlocksOnCalls(invToSpecCalls, spec);
        AbstractionLifter progAbs = new AbstractionLifter(spec, exprFactory, ctx, invToSpecCalls, cmdLine.getnUnroll(), breakBlocks.getReturnLocations());

        Transform recurElimT = new Transform("wjtp.recelim", recursionEliminator);
        Transform apiCallRewriteT = new Transform("wjtp.apirew", apiCallRewriter);
        Transform wildcardT = new Transform("wjtp.wct", wildcardTransformation);
        Transform localizeT = new Transform("wjtp.lct", localizeTransform);
        Transform programAbsT = new Transform("wjtp.abs", progAbs);
        Transform normBBsT = new Transform("wjtp.normbb", normBBs);
        Transform normRetT = new Transform("wjtp.normRet", normRet);
        Transform swRemoverT = new Transform("wjtp.swremov", swRemover);
        Transform assumeT = new Transform("wjtp.assume", assumify);
        Transform devirtT = new Transform("wjtp.devirt", devirt);
        Transform breakCallsT = new Transform("wjtp.breakb", breakBlocks);
        Transform writeSetT = new Transform("wjtp.writeSet", writeSetGenerator);

        wjtpPack.add(recurElimT);
        wjtpPack.add(apiCallRewriteT);
        wjtpPack.add(devirtT);
        wjtpPack.add(wildcardT);
        wjtpPack.add(localizeT);
        wjtpPack.add(programAbsT);
        wjtpPack.add(normBBsT);
        wjtpPack.add(normRetT);
        wjtpPack.add(swRemoverT);
        wjtpPack.add(assumeT);
        wjtpPack.add(breakCallsT);
        wjtpPack.add(writeSetT);

        VerifierUtil.calculateReachableMethods();

        swRemoverT.apply();
        normBBsT.apply();
        normRetT.apply();
        devirtT.apply();
        apiCallRewriteT.apply();
        wildcardT.apply();
        //writeSetT.apply();
        localizeT.apply();
        recurElimT.apply();
        assumeT.apply();
        breakCallsT.apply();
        writeSetT.apply();
        programAbsT.apply();

        InterpolantGenerator interpGen = new InterpolantGenerator(exprFactory, spec, ctx, breakBlocks.getReturnLocations());
        Checker cfpChecker = new Checker(spec, progAbs, interpGen);
        cfpChecker.check();
        */
        
        // Print classes out to file
        // Based on edu.utexas.cs.utopia.expresso.Driver
        log.debug("Writing transformed classes to files");
        for(String className : cmdLine.getTargetClasses()) {
        	SootClass targetClass = Scene.v().getSootClass(className);
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
}