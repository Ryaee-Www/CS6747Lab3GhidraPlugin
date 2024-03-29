#include "pin.H"
#include <iostream>
#include <fstream>
#include <map>
#include <set>

// Imagebase: 0x400000L
// Headers[start: 0x400000, end: 0x4003ff]
// .text  [start: 0x401000, end: 0x402dff]
// .rdata [start: 0x403000, end: 0x4039ff]
// .data  [start: 0x404000, end: 0x4047ff]
// .rsrc  [start: 0x405000, end: 0x4053ff]

std::ofstream OutFile;
bool instrumentationEnabled = false; // Global flag to control instrumentation

ADDRINT binaryStart = 0;
ADDRINT binaryEnd = 0;
ADDRINT targetAddress = 0x40297D; // The target address to start instrumentation
ADDRINT prevInstruction = 0; // Address of the previous instruction
std::map<ADDRINT, std::set<ADDRINT>> controlFlowGraph; // Map of instruction addresses to subsequent instruction addresses

// Callback function to be called for every instruction
VOID Instruction(INS ins, VOID* v)
{
    ADDRINT insAddress = INS_Address(ins);

    // Check if the instruction is within the main binary range
    if (insAddress >= binaryStart && insAddress <= binaryEnd) {
        // Check the instruction address against the target address
        if (insAddress == targetAddress) {
            instrumentationEnabled = true;
        }

        // If instrumentation is enabled, perform instrumentation logic
        if (instrumentationEnabled) {
            // If there is a previous instruction, update the control flow graph
            if (prevInstruction != 0) {
                controlFlowGraph[prevInstruction].insert(insAddress);
            }
            prevInstruction = insAddress; // Update the previous instruction to the current one
        }
    }
}


// This function is called when an image is loaded
VOID ImageLoad(IMG img, VOID* v)
{
    // Check if this is the main executable
    if (IMG_IsMainExecutable(img)) {
        binaryStart = IMG_LowAddress(img);
        binaryEnd = IMG_HighAddress(img);
    }
}


// Function to be called when the application exits
VOID Fini(INT32 code, VOID* v)
{
    OutFile << "digraph controlflow {" << std::endl;

    // Add the start and end address as a special node or comment
    //OutFile << "// Start Address: " << std::hex << binaryStart << std::endl;
    //OutFile << "// End Address: " << std::hex << binaryEnd << std::endl;

    // Add an extra newline for readability
    //OutFile << std::endl;

    // Iterate through the control flow graph and print edges
    for (const auto& pair : controlFlowGraph) {
        for (const auto& dest : pair.second) {
            OutFile << "     \"0x" << std::hex << pair.first << "\" -> \"0x" << std::hex << dest << "\";" << std::endl;
        }
    }
    OutFile << "  }" << std::endl;
    OutFile.close();
}


// Usage function
INT32 Usage()
{
    std::cerr << "This Pintool generates a file named submission.dot." << std::endl;
    std::cerr << "Usage:" << std::endl << "\tpin -t <toolname>.so -- <application>" << std::endl;
    return -1;
}


int main(int argc, char* argv[])
{
    // Initialize pin
    if (PIN_Init(argc, argv)) {
        return Usage();
    }

    OutFile.open("submission.dot");

    // Register the function to be called when the application exits
    PIN_AddFiniFunction(Fini, 0);

    // Register ImageLoad to be called when an image is loaded
    IMG_AddInstrumentFunction(ImageLoad, 0);

    // Register Instruction to be called to instrument instructions
    INS_AddInstrumentFunction(Instruction, 0);

    // Start the program, never returns
    PIN_StartProgram();

    return 0;
}
