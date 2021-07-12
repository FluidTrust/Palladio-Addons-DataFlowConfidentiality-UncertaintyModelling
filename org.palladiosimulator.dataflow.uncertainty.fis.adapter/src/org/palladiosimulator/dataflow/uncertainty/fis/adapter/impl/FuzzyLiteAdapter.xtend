package org.palladiosimulator.dataflow.uncertainty.fis.adapter.impl

import org.palladiosimulator.dataflow.uncertainty.fis.adapter.FuzzySystemExecution
import java.util.List
import java.lang.ProcessBuilder.Redirect
import java.io.IOException
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import org.apache.commons.lang3.SystemUtils
import java.util.Optional
import java.io.File
import org.apache.commons.io.FileUtils
import java.util.regex.Pattern

class FuzzyLiteAdapter implements FuzzySystemExecution {
	var fuzzylitePath = ""
	
	new () {
		var executable = extractExecutable
		if(!executable.empty) {
			fuzzylitePath = executable.get.absolutePath
		}
	}
	
	override runFIS(List<Double> inputs, Path fisPath) {
		var dataPath = createDataFile(inputs)
		var resultPath = runSystem(fisPath, dataPath)
		var output = parseOutputFromResultFile(resultPath)
		
		return output
	}
	
	private def createDataFile(List<Double> data) {
		try {
			var line = String.join(" ", data.map[d| Double.toString(d)])
            var tempFile = Files.createTempFile("tmpFISInputs", ".fld");
            Files.deleteIfExists(tempFile);
            Files.write(tempFile, line.getBytes(StandardCharsets.UTF_8));
            
            return tempFile
        } catch (IOException e) {
            e.printStackTrace
        }
	}
	
	private def runSystem(Path systemPath, Path dataPath) {
	    try {
	    	var resultPath = Files.createTempFile("tmpFISOutput", ".fld");
	    	Files.deleteIfExists(resultPath);
	        val pb = new ProcessBuilder(fuzzylitePath, "-i", systemPath.toString, "-of", "fld", "-o", resultPath.toString, "-d", dataPath.toString)
	        pb.redirectOutput(Redirect.DISCARD)
	        pb.redirectError(Redirect.DISCARD)
	        val process = pb.start()
	        process.waitFor();
	        
	        return resultPath
	    } catch(IOException e) {
	        e.printStackTrace
	    }
	}
	
	private def parseOutputFromResultFile(Path resultFilePath) {
		var result = readResultFile(resultFilePath)
		
		// The regex finds the last floating point number in the result string
		var regexPattern = Pattern.compile("\\d*\\.\\d*$")
		var matcher = regexPattern.matcher(result)
		var String outputValue = ""
		while(matcher.find()) {
			outputValue = matcher.group
		}
		
		try {
			return Double.parseDouble(outputValue)
		} catch (NumberFormatException e) {
			// Value is not formated as a double
			// remove for testing randomly created FIS
			//System.err.println("Result is NaN. FIS rules do not create a that can be defuzzyfied (possibly no rule applies with the given inputs and the fuzzy output is 0 across the whole range). ")
		}
		
		return Double.NaN
	}
	
	private def readResultFile(Path resultPath) {
		try {
			var resultFileContent = Files.readString(resultPath);
        	return resultFileContent
		} catch (IOException e) {
			e.printStackTrace
		}
	}

	private def String getFileName() {
		var os = "";
		var ending = "";
		if (SystemUtils.IS_OS_WINDOWS) {
			os = "win";
			ending = ".exe";
		} else if (SystemUtils.IS_OS_LINUX) {
			os = "linux";
			ending = "";
		}
		var version = "6.0";
		var architecture = "x64";
		return String.format("fuzzylite-%s-%s-%s%s", version, os, architecture, ending);
	}
	
	private def Optional<File> extractExecutable() {
		var ClassLoader cl = FuzzyLiteAdapter.classLoader
		var execFileName = getFileName
		var execInStream = cl.getResourceAsStream(execFileName) 
		if(execInStream === null) {
			return Optional.empty
		}
		try {
			var execFilePath = Files.createTempFile(execFileName, "")
	        var execFile = execFilePath.toFile
	        
	        FileUtils.copyInputStreamToFile(execInStream, execFile)
	        
	        execFile.deleteOnExit
	        execFile.setExecutable(true)
			
			return Optional.of(execFile)
		} catch (IOException e) {
			e.printStackTrace
		} finally {
			execInStream.close
		}
		
		return Optional.empty
	}
}