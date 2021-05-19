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
import java.io.InputStream
import org.apache.commons.io.FileUtils

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
		
		var split = result.split("\n")
		if(split.size == 2) {
			var resultLine = split.get(1).split(" ")
			if(resultLine.size == 3) {
				try {
					return Double.parseDouble(resultLine.get(2))
				} catch (NumberFormatException e) {
					// Value is not formated as a double
					// should never occur
					e.printStackTrace
				}
			}
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
		var cl = FuzzyLiteAdapter.classLoader
		var execFileName = getFileName
		if (cl.getResource(execFileName) === null) {
			return Optional.empty
		}
		
		var InputStream execInStream 
		try {
			execInStream = cl.getResourceAsStream(execFileName) 
			var execFilePath = Files.createTempFile(execFileName, "")
	        var execFile = execFilePath.toFile
	        execFile.deleteOnExit
	        
	        var byte[] execFileBytes = execInStream.readAllBytes
	        FileUtils.writeByteArrayToFile(execFile, execFileBytes)
	        
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