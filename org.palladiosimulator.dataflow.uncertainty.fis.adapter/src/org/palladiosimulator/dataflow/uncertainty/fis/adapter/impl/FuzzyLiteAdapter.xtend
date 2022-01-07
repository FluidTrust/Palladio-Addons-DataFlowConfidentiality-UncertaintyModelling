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
import java.util.ArrayList
import java.nio.file.Paths

class FuzzyLiteAdapter implements FuzzySystemExecution {
	
	var Path tmpExecutionDir
	var String fuzzylitePath = ""
	
	new () {
		// Create temp directory and delete it at exit
		tmpExecutionDir = Files.createTempDirectory("FuzzyLiteExec")
		tmpExecutionDir.toFile.deleteOnExit
		
		var executable = extractExecutables
		if(!executable.empty) {
			fuzzylitePath = executable.get.absolutePath
		}
	}
	
	/**
	 * Runs the FIS under fisPath with the provided inputs
	 */
	override runFIS(List<Double> inputs, Path fisPath) {
		var dataPath = createDataFile(inputs)
		var resultPath = runSystem(fisPath, dataPath)
		var output = parseOutputFromResultFile(resultPath)
		
		return output
	}
	
	private def createDataFile(List<Double> data) {
		try {
			var line = String.join(" ", data.map[d| Double.toString(d)])
			
			var tempFile = createTempFileInTempDir("tmpFISInputs.fld")
            Files.write(tempFile, line.getBytes(StandardCharsets.UTF_8))
            
            return tempFile
        } catch (IOException e) {
            e.printStackTrace
        }
	}
	
	// Run fuzzylite executable; output file is created first to ensure that there is no duplicate
	private def runSystem(Path systemPath, Path dataPath) {
	    try {
	    	var resultPath = createTempFileInTempDir("tmpFISOutput.fld");
	        val pb = new ProcessBuilder(fuzzylitePath, "-i", systemPath.toString, "-of", "fld", "-o", resultPath.toString, "-d", dataPath.toString)
	        pb.redirectOutput(Redirect.DISCARD)
	        pb.redirectError(Redirect.DISCARD)
	        val process = pb.start()
	        process.waitFor()
	        
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
			var resultFileContent = Files.readString(resultPath)
        	return resultFileContent
		} catch (IOException e) {
			e.printStackTrace
		}
	}
	
	private def ArrayList<String> getExecFileNames() {
		var fileNames = new ArrayList
		
		if (SystemUtils.IS_OS_WINDOWS) {
			fileNames.add("fuzzylite.exe")
			fileNames.add("fuzzylite.dll")
		} else if (SystemUtils.IS_OS_LINUX || SystemUtils.IS_OS_MAC) {
			fileNames.add("fuzzylite")
		}
		return fileNames
	}
	
	private def Optional<File> extractExecutables() {
		var execFileNames = getExecFileNames
		var Optional<File> execFile = null
		for(fileName : execFileNames) {
			var tmpFile = extractFile(fileName)
			
			// First filename in execFileNames is the actual executable
			if(execFile === null) {
				execFile = tmpFile
			}
		}
		
		return execFile
	}
	
	private def Optional<File> extractFile(String fileName) {
		var ClassLoader cl = FuzzyLiteAdapter.classLoader
		var execInStream = cl.getResourceAsStream(fileName)
		if(execInStream === null) {
			return Optional.empty
		}
		try {
			var filePath = createTempFileInTempDir(fileName)
	        var file = filePath.toFile
	        
	        FileUtils.copyInputStreamToFile(execInStream, file)
	        file.setExecutable(true)
			
			return Optional.of(file)
		} catch (IOException e) {
			e.printStackTrace
		} finally {
			execInStream.close
		}
		
		return Optional.empty
	}
	
	// Creates temp file in temp folder that deletes on exit
	private def Path createTempFileInTempDir(String fileName) {
		var filePath = Paths.get(this.tmpExecutionDir + File.separator + fileName)
		Files.deleteIfExists(filePath)
		filePath = Files.createFile(filePath)
        filePath.toFile.deleteOnExit
        
        return filePath
	}
}