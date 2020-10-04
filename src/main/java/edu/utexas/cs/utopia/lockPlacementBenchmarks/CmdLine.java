package edu.utexas.cs.utopia.lockPlacementBenchmarks;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;

/**
 * Based on edu.utexas.cs.utopia.cfpchecker.CmdLine by kferles
 * 
 * Holds command line arguments for this project
 */
public class CmdLine
{
    private int localCost = 1;
    private int globalCost = 2;
    private boolean debugZ3 = false;
	private boolean isHelp = false;
    private ArrayList<String> targetClasses = new ArrayList<String>();
    
    public String usage()
    {
        StringBuilder rv = new StringBuilder();

        rv.append("java -jar lockPlacementBenchmarks.jar targetsFile <monitorClassName> -- [soot-options]\n")
          .append("targetsFile                  text file of of target class names, one on each line\n")
          .append("-lc, -localCost localCost    An integer to weight the conflict from a local lock, default 1\n")
          .append("-gc, -globalCost globalCost  An integer to weight the conflict from a global lock, default 2\n")
          .append("-debugZ3                     log the Z3 formula at the debug level")
          .append("-h, --help:                  print this message and exit\n");

        return rv.toString();
    }

    public String parseArgs(String[] args)
    {
        String parseError = null;
        
        if(args.length == 0) {
        	parseError = "Missing targetsFile\n";
        }
        else {
        	try (BufferedReader reader = Files.newBufferedReader(Paths.get(args[0]))) {
        		String line = reader.readLine();
        		while(line != null) {
        			targetClasses.add(line);
        			line = reader.readLine();
        		}
        	}
        	catch(IOException e) {
        		e.printStackTrace();
        		System.exit(1);
        	}
        }

        parseLoop:
        for (int i = 1; i < args.length; )
        {
        	switch (args[i])
            {
            	case "-lc":
            	case "-localCost":
            		localCost = Integer.parseInt(args[++i]);
            		++i;
            		break;
            	case "-gc":
            	case "-globalCost":
            		globalCost = Integer.parseInt(args[++i]);
            		++i;
            		break;
            	case "-debugZ3":
            		debugZ3 = true;
            		++i;
            		break;
            	case "-h":
                case "--help":
                    isHelp = true;
                    break parseLoop;
                default:
                    parseError = "Invalid option: " + args[i];
                    break parseLoop;
            }
        }

        return parseError;
    }
    
    public ArrayList<String> getTargetClasses() {
    	return targetClasses;
    }

    public boolean isHelp()
    {
        return isHelp;
    }

    /**
     * @return the localCost
     */
	public int getLocalCost() {
		return localCost;
	}

	/**
	 * @return the globalCost
	 */
	public int getGlobalCost() {
		return globalCost;
	}

	/**
	 * @return true iff debugZ3 is set
	 */
	public boolean getDebugZ3() {
		return debugZ3;
	}
}
