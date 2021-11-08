# Palladio-Addons-DataFlowConfidentiality-UncertaintyModelling
Project and package names have been chosen following the naming of the data flow diagramm approach of Seifermann et al. [1], which we base our implementation on.

## Prerequisites:
To build this project and run the included tests for evaluation the following reqirements need to be met:
- Java version 11 needs to be installed **and** set as default version
- Maven needs to be installed
- Depending on the operating system:
	- Linux: cmake needs to be installed
	- Windows: cmake and nmake need to be installed (e.g. via [Buildtools für Visual Studio](https://visualstudio.microsoft.com/de/downloads/))

## Build Fuzzy Logic Libraries:
Currently, we support the use of FuzzyLite 6.0 operating systems.
1. Download the sources of [fuzzy lite](https://www.fuzzylite.com/downloads/).
2. Extract the archive.
3. Inside, open the *INSTALL* file with a text editor and follow the instructions to build the executable.
4. Afterwards, maneuver to the `./fuzzylite-6.0/fuzzylite/release/bin/` folder.
5. Copy the executables in the `./org.palladiosimulator.dataflow.uncertainty.fis.adapter/fuzzylite/` folder. Depending on the operating system: 
	- Linux: fuzzylite
	- Windows: fuzzylite.exe **and** fuzzylite.dll
	
## Build and Run Tests:
After the fuzzy logic libraries have been built and copied in the right folder, open a command line in this folder and run `mvn install`. This command builds the project and also runs the included tests.

## Import in Eclipse:
The source code can also be imported and executed in Eclipse. 
Download and open [Eclipse Modeling Edition 2020-12](https://www.eclipse.org/downloads/packages/release/2020-12/r/eclipse-modeling-tools). 
Open the *Install New Software* dialog in Eclipse and press the button *Manage..* in the top right. In the newly opened window press the *Import...* button. Select the included *updatesites.xml* in the import dialog, to import the information for all update sites necessary.
Now use the *Install New Software* dialog to install the following requirements from the imported update sites:

| Update Site | Package Name |
|--|--|
| Palladio 5.0 release | - Palladio Bench Addons |
|  | - Palladio Core Features |
|  | - Palladio Supporing Features |
| Orbit 2020-12 | - Apache Commons Lang |
|  | - Hamcrest library |
| Itemis Xtext | - Xtext Antlr |
| Prolog | - Palladio Supporting Features |
| Prolog4J | - Prolog4J |
| Data Flow Diagram | - Data Flow Diagram |
| Data Flow Diagram Confidentiality | - Dataflow Diagram Confidentiality |
| Maven Integration | - Maven Integration for Eclipse |
| MDSD Tools Standalone Init | - MDSD Tools Standalone Initialization |
| MDSD Tools EcoreWorkflow | - MDSD Tools Ecore Workflow |
| Latest Eclipse Release | - Modeling -> Xtext Complete SDK |

To run the test the fuzzy logic libraries still need to be build (see above).

## Bibliography
[1] Stephan Seifermann et al. "Detecting Violations of Access Control and Information Flow Policies in DataFlow Diagrams". In: Journal of Systems and Software (2021). DOI: [10.5445/IR/1000139064](https://publikationen.bibliothek.kit.edu/1000139064). Accepted.
