# Palladio-Addons-DataFlowConfidentiality-UncertaintyModelling
This replication package includes the source code, tests and corresponding model instances.

Project and package names have been chosen following the naming of the data flow diagramm approach of Seifermann et al. [1], which we base our implementation on.

## Requirements:
To build this project and run the included tests for evaluation the following reqirements need to be met:
- Java version 11 needs to be installed **and** set as default version
- Maven needs to be installed
- Depending on the operating system:
	- Linux: cmake needs to be installed
	- Windows: cmake and nmake need to be installed (e.g. via [Buildtools für Visual Studio](https://visualstudio.microsoft.com/de/downloads/))

## Build Fuzzy Logic Libraries:
Currently, we support the use of FuzzyLite 6.0 operating systems.

1. Download the sources of fuzzy lite [Link](https://www.fuzzylite.com/downloads/).
2. Extract the archive.
3. Inside, open the *INSTALL* file with a text editor and follow the instructions to build the executable.
4. Afterwards, maneuver to the `./fuzzylite-6.0/fuzzylite/release/bin/` folder.
5. Copy the executables in the `./org.palladiosimulator.dataflow.uncertainty.fis.adapter/fuzzylite/` folder. Depending on the operating system: 
	- Linux: fuzzylite
	- Windows: fuzzylite.exe **and** fuzzylite.dll
	
## Build and Run Tests:
After the fuzzy logic libraries have been built and copied in the right folder, open a command line in this folder and run `mvn install`. This command builds the project and also runs the included tests.

## Bibliography
[1] Stephan Seifermann et al. "Detecting Violations of Access Control and Information Flow Policies in DataFlow Diagrams". In: Journal of Systems and Software (2021). DOI: [10.5445/IR/1000139064](https://publikationen.bibliothek.kit.edu/1000139064). Accepted.
