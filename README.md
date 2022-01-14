# Palladio-Addons-DataFlowConfidentiality-UncertaintyModelling

This project contains the extension code of the master thesis [Architectural Uncertainty Analysis for Access Control Scenarios in Industry 4.0](https://publikationen.bibliothek.kit.edu/1000135847). The aim is to include uncertainty into the approach developed in [Detecting Violations of Access Control and Information Flow Policies in Data Flow Diagrams](https://publikationen.bibliothek.kit.edu/1000139064).  

## Research projects

- [Palladio](https://www.palladio-simulator.com/home/): software architecture simulation approach which analyses your software at the model level for performance bottlenecks, scalability issues, reliability threats, and allows for a subsequent optimisation 
- [FluidTrust](https://fluidtrust.ipd.kit.edu/home/): enabling trust by fluid access control to data and physical resources in Industry 4.0 systems


## Project description
The code in this repository can be used to run confidentiality analyses of exemplary data flow diagrams including uncertainty.

The repository is based on the repositories: 
- [Palladio-Supporting-DataFlowDiagram](https://github.com/FluidTrust/Palladio-Supporting-DataFlowDiagram)
- [Palladio-Supporting-DataFlowDiagramConfidentiality](https://github.com/FluidTrust/Palladio-Supporting-DataFlowDiagramConfidentiality/tree/uncertainty-integration)

The first repository adds support of data flow diagrams in Palladio. The second repository allows to run the confidentiality analyses based on the data flow diagrams. The approach is described in the publication [Detecting Violations of Access Control and Information Flow Policies in Data Flow Diagrams](https://publikationen.bibliothek.kit.edu/1000139064) and examples of used data flow diagrams can be found [on this link](https://zenodo.org/record/5535599#.YYT0z2DMKiM).

This repository adds uncertainty to the confidentiality analyses of data flow diagrams.     


## Project setup

### Setup Eclipse 
- Install [Eclipse](https://www.eclipse.org/) 
- Install [Eclipse Modeling Tools 2020-12](https://www.eclipse.org/downloads/packages/release/2020-12/r/eclipse-modeling-tools)


### Java and Maven requirements
To build this project and run the included tests for evaluation you need:
- Install [Java version 11.0.3](https://www.oracle.com/java/technologies/java-se-development-kit11-downloads.html) **and** set as default version (other Java versions may not be supported)
- Install [Maven](https://maven.apache.org/download.cgi) 


### Clone repositories and add to Eclipse Workspace

- Clone the repositories: 
	1. [Palladio-Supporting-DataFlowDiagram](https://github.com/FluidTrust/Palladio-Supporting-DataFlowDiagram) 
	2. [Palladio-Supporting-DataFlowDiagramConfidentiality](https://github.com/FluidTrust/Palladio-Supporting-DataFlowDiagramConfidentiality/tree/uncertainty-integration) - Make sure to directly clone the uncertainty-integration branch (as linked above) from the 2. repository with `git clone -b uncertainty-integration ...` (switching to uncertainty-integration branch after cloning the master branch can cause Eclipse problems)
	3. [this repository](https://github.com/FluidTrust/Palladio-Addons-DataFlowConfidentiality-UncertaintyModelling) in one folder
- Create new Eclipse Workspace 
- Import all three repositories: 
	- Open in the menu *File* > Import > General > *Existing Projects into Workspace*
	- Select your root directory
	- Under Options, check `Search for nested projects` to correctly import repo (ii.)


### Installation of new software within Eclipse 
- In the Eclipse menu: select Help > *Install New Software* 
- Press the button *Manage..* in the top right 
- Press the *Import...* button 
- Select the *updatesites.xml* from this repository in the import dialog. This imports the information for all necessary update sites/Eclipse software. hint: this does not install the update sites 
- Use the *Install New Software* dialog (*Work with* dropdown) to install the following update sites:

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

Hint: to run the test the fuzzy logic libraries still need to be build (see next section).


### Build Fuzzy Logic library:
The library FuzzyLite enables uncertainty in the confidentiality analyses of the data flow diagrams. It needs to be compiled with cmake (see requirements)

1. Install [cmake](https://cmake.org/download/), depending on your [operating system Windows, MacOS or Linux](https://cmake.org/install/) 
2. Download the sources of FuzzyLite 6.0 [Link](https://www.fuzzylite.com/downloads/), accordingly to your operating system.
3. Extract the archive.
4. Inside, open the *INSTALL* file with a text editor and follow the instructions to build the executable.
5. After installation, maneuver to the `./fuzzylite-6.0/fuzzylite/release/bin/` folder.
6. Copy the executables in the `./org.palladiosimulator.dataflow.uncertainty.fis.adapter/fuzzylite/` folder. Depending on the operating system: 
	- Windows: fuzzylite.exe **and** fuzzylite.dll
	- Linux/MacOS: fuzzylite


### Rectify Eclipse problems / generate java classes from EMF: 
The Java classes still need to be generated from the models made with the Eclipse Modeling Framework (EMF).
- In the project `org.palladiosimulator.dataflow.diagram.mwe2` of repo (i.), run `workflow/generate.mwe2` as MWE2 Workflow
- In the project `org.palladiosimulator.dataflow.confidentiality.mwe2` of repo (ii.) uncertainty-integration branch, run `workflow/generate.mwe2` and `workflow/GenerateCharacterizedDataDictionary.mwe2` as MWE2 Workflow
- In the project `org.palladiosimulator.dataflow.uncertainty.mwe2` of this repo (iii.), run `workflow/generate.mwe2` as MWE2 Workflow
   

### Build and Run Tests:
Run `mvn clean install`. This command builds the project and also runs the included tests.


## How to use the project
...


## Problems log 
### Open problems
- TrustAccuracyAnalysisTest - 7/8 tests fail: reason is a higher number of solutions than expected
- RunningExapleACTest - testRunningExampleScenario2 fail: reason is a higher number of solutions than expected
- Eclipse error in pom.xml of `org.palladiosimulator.dataflow.uncertainty.mwe2` in repo (iii.): `Plugin execution not covered by lifecycle configuration` and `unknown packaging: eclipse-plugin`

### Solutions
- For several Eclipse problems and warnings: Open in the menu *Project* > Clean


## Bibliography
[1] Nicolas Boltz. "Architectural Uncertainty Analysis for Access Control Scenarios in Industry 4.0". 2021. DOI: [10.5445/IR/1000135847](https://publikationen.bibliothek.kit.edu/1000135847).
[2] Stephan Seifermann et al. "Detecting Violations of Access Control and Information Flow Policies in DataFlow Diagrams". In: Journal of Systems and Software (2021). DOI: [10.5445/IR/1000139064](https://publikationen.bibliothek.kit.edu/1000139064). Accepted.
