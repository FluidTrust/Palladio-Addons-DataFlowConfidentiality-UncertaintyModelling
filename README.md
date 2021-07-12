# Palladio-Addons-DataFlowConfidentiality-UncertaintyModelling

## Build:
To build this project, fuzzy logic libraries need to build and added by hand manually. Currently, we support the use of FuzzyLite 6.0 on x64 operating systems.
1. Download the sources of fuzzy lite [Link](https://www.fuzzylite.com/downloads/)
2. Extract the archive
3. Inside, open the 'INSTALL' file with a text editor and follow the instructions to build the executable
4. Afterwards, maneuver to the ./fuzzylite-6.0/fuzzylite/release/bin/ folder
5. Depending on the operating system, rename the contained 'fuzzylite' file to either
    * fuzzylite-6.0-linux-x64
    * fuzzylite-6.0-win-x64.exe
6. Copy the executable in the ./org.palladiosimulator.dataflow.uncertainty.fis.adapter/fuzzylite/ folder

