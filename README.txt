Installation
1. Extract the zip file to a folder of your choosing.
2. Create a new workspace in Eclipse, make a new project and import the included src folder.
3. Right click the project, choose 'Properties', and select 'Build Path' on the left.
4. Go to the Libraries tab. Choose 'Add External JARs', and navigate to the lib folder we included. Select all JARs and add them.
5. While still in the properties window, navigate to 'Java Compiler' on the left, and select 'Errors/Warnings'. 
6. Set all selection boxes under 'Deprecated and restricted API' to 'ignore'.


Testing
The JUnit tests are present in the test folder.


Starting the game
Open a terminal at the folder of installation
Type "java -jar Connect4.jar [tui/gui]"
tui for the Textual User Interface, gui for the Graphical User Interface
If you can't start the gui please use a different laptop/desktop, we couldn't get it to work with 1 computer ourselves. (Something with pipeline initialization error)