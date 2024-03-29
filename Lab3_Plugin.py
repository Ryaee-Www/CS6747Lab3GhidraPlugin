"""
Data Dependence Algorithm:
1. Enhance the analyze_instruction function to accurately capture all definitions and uses of variables.
    - Fix existing bugs in the function.
2. Traverse the Control Flow Graph (CFG): Implement a method to traverse the CFG to find dependencies based on the collected definitions and uses.
    - For functions with multiple RET instructions, enumerate paths for each RET. Consider using a recursive reverse search of the CFG.
    - Each path should start from "START"
    - To avoid the path explosion problem often encountered with loops, set a loop unrolling limit (execute each loop at least twice).
    - Ensure full path coverage, including cycles and cycles within cycles.
3. Identify the Most Recent Definition of a Variable: For each instruction along the path, find the most recent definition of a variable before its use by traversing the path backward.
4. Modify the output to include data dependencies for each instruction.
5. Generate a data dependency graph in DOT format.

General Principles:
- If a register or pointer has not been modified in the function, data dependence is on START.
- The CFG should be followed in reverse instead of linear search to ensure that conditional jumps do not disrupt the algorithm.

Algorithm should roughly be as below:
- Register input: DD on the most recent instruction that defines the register.
- Pointer input: DD on the most recent instruction that defines the register AND the most recent instruction that defines the data held at that pointer.
- Conditional Jumps: DD on the most recent instruction that defines the relevant Flag (e.g., SUB, CMP, TEST).
- Address Input: DD on the address.
- POP instruction: POP takes a value (uses ESP and takes the most recent value). Depends on the current value of ESP and the value it will be popping from the stack.
- PUSH instruction: PUSH adds a value (uses ESP and defines a new value), DD on the most recent POP/PUSH and the dependency on whatever value they're pushing.

Example:
MOV EAX, 0x1 -> DD: 
MOV ECX, 0x2 -> DD:
PUSH ECX -> DD: 2, START
PUSH EAX -> DD: 3,1
POP ECX -> DD: 4
POP EAX-> DD: 5, 3
"""

import os
import re
from ghidra.program.model.block import BasicBlockModel
from ghidra.program.model.lang import OperandType, Register
import ghidra.program.model.symbol.RefType as RefType
import ghidra.util.task.ConsoleTaskMonitor as ConsoleTaskMonitor
from ghidra.program.model.lang import Register

functions_count = 0
addresses_count = 0
instructions_count = 0
instruction_def_use = {}


class DDStorage():
    def __init__(self):
        # self.uses = {}
        self.defs = {}  # {regester/pointer offset: address}

    def has(self, register):
        return register in self.defs

    def getAddress(self, register):
        return self.defs[register]

    def newDefine(self, register, address):
        self.defs[register] = address

    def processDataDep(self, uses, defs, addr):
        '''
            Processes one line of assembly code. should be called in a loop to process every line in a basic block

            @param uses: a list of 'USE', contains register, or an pointer offset, data, etc. that is used in the assembly code
            @param defs: a list of 'DEF', same as 'USE', that is defined or modified in the assembly code
            @param addr: a string that represents the address of the current line of assembly code.
            @param DDStorage, an object contains all previously defined registers, each basic block should have its own Storage object(?)

            @return: a list of data dependency, in form of ["address"], contains "START" if used
            '''
        dependsOn = []
        print("DEBUG PDD: ", uses, defs, addr)
        for i in uses:
            if self.has(i):
                dependsOn.append(self.getAddress(i))
            else:
                if 'START' not in dependsOn:
                    dependsOn.append('START')
        for i in defs:
            self.newDefine(i, addr)

        return dependsOn

def create_dot_graph(func, instruction_list, jumps, conditional_jumps, ret_instructions, def_use_info):
    """
    Generates a DOT graph representation of the control flow within a function.
    """
    # Convert the entry point of the function to a hexadecimal string
    entry_point = "0x{}".format(func.getEntryPoint().toString().lstrip('0'))
    dot_graph = 'digraph "{}" {{\n'.format(entry_point)
    node_counter = 1
    address_to_node = {}  # Maps addresses to node names

    # Create graph nodes for each instruction address
    for addr in instruction_list:
        node_name = 'n{}'.format(node_counter)
        addr_label = "0x{}".format(addr)  # Ensure '0x' prefix
        # Assign a label with define-use information if available
        if addr in def_use_info:
            label = "{}; {}".format(addr_label, def_use_info[addr])
        else:
            label = "{};".format(addr_label)
        dot_graph += '    {} [label = "{}"];\n'.format(node_name, label)
        address_to_node[addr] = node_name
        node_counter += 1

    dot_graph += '\n'  # Separate nodes from edges

    # Add edges between nodes based on sequential and jump instructions:
    for i, addr in enumerate(instruction_list):
        if addr in ret_instructions:  # Skip edge creation for RET instructions
            continue
        if i + 1 < len(instruction_list):
            current_node = address_to_node[addr]
            next_addr = instruction_list[i + 1]
            next_node = address_to_node[next_addr]

            # Check if the current instruction is a jump and add an edge accordingly
            if addr in jumps:
                jump_to_node = address_to_node[jumps[addr]]
                # Draw line for jump with style based on jump type
                # jump_style = 'conditional_jump' if addr in conditional_jumps else 'unconditional_jump'
                # dot_graph += '    {} -> {}; [{}]\n'.format(current_node, jump_to_node, jump_style)
                dot_graph += '    {} -> {};\n'.format(current_node, jump_to_node)

                # For conditional jumps, also connect to the next sequential instruction
                if addr in conditional_jumps:
                    dot_graph += '    {} -> {};\n'.format(current_node, next_node)
            elif next_node:  # Ensure sequential flow except for RET instructions
                dot_graph += '    {} -> {};\n'.format(current_node, next_node)

    dot_graph += '}'
    return dot_graph


def create_dot_graph_DD(func, instruction_list, jumps, conditional_jumps, ret_instructions, dependsOn):
    """
    Generates a DOT graph representation of the control flow within a function.
    """
    # Convert the entry point of the function to a hexadecimal string
    def sort_key(item):
        match = re.search(r'n(\d+)', item)
        if match:
            return int(match.group(1))
        return float('inf')
    entry_point = "0x{}".format(func.getEntryPoint().toString().lstrip('0'))
    dot_graph = 'digraph "{}" {{\n'.format(entry_point)
    node_counter = 1
    address_to_node = {}  # Maps addresses to node names

    # Create graph nodes for each instruction address
    for addr in instruction_list:
        # insert n0
        if len(address_to_node) == 0:
            node_name = 'n0'
            addr_label = "START"
            address_to_node[addr_label] = node_name
            label = "START"
            dot_graph += '    {} [label = "{}"];\n'.format(node_name, label)

        # insert normal n1 & beyond
        node_name = 'n{}'.format(node_counter)
        addr_label = "0x{}".format(str(addr))  # Ensure '0x' prefix
        # Assign a label with define-use information if available
        if addr in dependsOn:
            label = "{}; DD: {}".format(addr_label, ', '.join(map(lambda x: '0x' + x if x != "START" else x, dependsOn[addr])))
        else:
            label = "{};".format(addr_label)
        dot_graph += '    {} [label = "{}"];\n'.format(node_name, label)
        address_to_node[addr] = node_name
        node_counter += 1

    dot_graph += '\n'  # Separate nodes from edges

    # Add edges between nodes based on sequential and jump instructions:

    allDep = []
    #print(address_to_node.items())
    for addr, node in address_to_node.items():
        #print(addr, node)
        if addr != "START":
            for thisDependent in dependsOn[addr]:
                if thisDependent == "START":
                    allDep.append('{} -> {}'.format(node, 'n0'))
                else:
                    allDep.append('{} -> {}'.format(node, address_to_node[thisDependent]))
    allDep = sorted(allDep, key=sort_key)
    for i in allDep:
        dot_graph += '    {};\n'.format(i)
    dot_graph += '}'
    return dot_graph



def operandRegisterHelper(instruction, defs, uses, addr_str):
    numOperand = instruction.getNumOperands()
    for i in range(numOperand):
        operand = instruction.getRegister(i)
        opType = instruction.getOperandRefType(i)

        # Check if operand is a register and update uses/defs lists accordingly
        if operand is not None:
            if opType.isConditional() and opType.isFlow():
                if "eflags" not in uses:
                    uses.append("eflags")
            if opType.isRead() and str(operand) not in uses:
                uses.append(str(operand))
            if opType.isWrite() and str(operand) not in defs:
                defs.append(str(operand))

        # Handle memory references involving registers
        else:
            thisDynamic = ''
            isPart = False
            isInstance = False
            isRead = False
            isWrite = False
            eor = False
            refListing = instruction.getDefaultOperandRepresentationList(i)
            for element in refListing:
                if isPart:
                    thisDynamic += str(element)
                if element == '[':
                    isPart = True
                    thisDynamic += str(element)
                if element == ']':
                    isPart = False
                    eor = True
                if isinstance(element, Register):
                    isInstance = True
                    if opType.isRead():
                        isRead = True
                        if str(element) not in uses:
                            uses.append(str(element))
                    if opType.isWrite():
                        isWrite = True
                        if str(element) not in defs:
                            defs.append(str(element))
                if isInstance and eor:
                    if (thisDynamic not in uses) and isRead:
                        uses.append(thisDynamic)
                    if (thisDynamic not in defs) and isWrite:
                        defs.append(thisDynamic)


def analyze_instruction(instruction, addr_str):
    """
    # Define a set of mnemonics (assembly instructions) to be analyzed.
    mnemonicSet = {'ADD', 'AND', 'CALL', 'CMP', 'DEC', 'IMUL', 'INC', 'JA', 'JBE', 'JC', 'JG', 'JL', 'JLE', 'JMP',
                   'JNC', 'JNZ', 'JZ', 'LEA', 'LEAVE', 'MOV', 'MOVSX', 'MOVZX', 'OR', 'POP', 'PUSH', 'RET', 'SAR',
                   'SETNZ', 'SHR', 'STOSD.REP', 'SUB', 'TEST', 'XOR'}
    """
    global instruction_def_use
    mnemonic = instruction.getMnemonicString()
    defs = []  # List to hold defined variables
    uses = []  # List to hold used variables

    operandRegisterHelper(instruction, defs, uses, addr_str)
    if mnemonic == 'CALL':
        callTargetRepresentation = instruction.getDefaultOperandRepresentation(0)
        addressMatch = re.search(r'\[([0-9a-fx]+)\]', callTargetRepresentation, re.IGNORECASE)
        if addressMatch:
            callTarget = '[{}]'.format(addressMatch.group(1))
        else:
            callTarget = callTargetRepresentation
        uses.append(callTarget)
    # Analyze instruction based on its type and collect define-use information
    elif mnemonic == 'ADD' or mnemonic == 'SUB':
        if 'eflags' not in defs:
            defs.append('eflags')
    elif mnemonic == 'AND' or mnemonic == 'OR' or mnemonic == 'XOR':
        if 'eflags' not in defs:
            defs.append('eflags')
    elif mnemonic == 'CMP':
        if 'eflags' not in defs:
            defs.append('eflags')
    elif mnemonic == 'IMUL' or mnemonic == 'MUL':
        if 'eflags' not in defs:
            defs.append('eflags')
    elif mnemonic == 'INC' or mnemonic == 'DEC':
        if 'eflags' not in defs:
            defs.append('eflags')
    elif mnemonic in ['JA', 'JZ', 'JBE', 'JC', 'JG', 'JL', 'JLE', 'JNC', 'JNZ']:
        if 'eflags' not in uses:
            uses.append('eflags')
    elif mnemonic == 'JMP':
        pass
    elif mnemonic == 'LEA':
        destReg = instruction.getRegister(0)
        if destReg is not None and str(destReg) not in defs:
            defs.append(str(destReg))
        sourceOperand = instruction.getDefaultOperandRepresentation(1)
        memoryRefMatch = re.search(r'\[(.*?)\]', sourceOperand)
        foundRegisters = set(re.findall(r'\b([a-zA-Z]+)\b', memoryRefMatch.group(1)))
        for reg in foundRegisters:
            if reg not in uses:
                uses.append(reg)
    elif mnemonic == 'LEAVE':
        defs.append('EBP')
        defs.append('ESP')
        uses.append('EBP')
        uses.append('[EBP]')
    elif mnemonic == 'MOV':
        pass
    elif mnemonic == 'MOVSX':
        pass
    elif mnemonic == 'MOVZX':
        pass
    elif mnemonic == 'POP':
        if 'ESP' not in defs:
            defs.append('ESP')
        if '[ESP]' not in uses:
            uses.append('[ESP]')
        if 'ESP' not in uses:
            uses.append('ESP')
    elif mnemonic == 'PUSH':
        if 'ESP' not in defs:
            defs.append('ESP')
        if '[ESP]' not in defs:
            defs.append('[ESP]')
        if 'ESP' not in uses:
            uses.append('ESP')
    elif mnemonic == 'RET':
        if 'ESP' not in uses:
            uses.append('ESP')
        if '[ESP]' not in uses:
            uses.append('[ESP]')
        if 'ESP' not in defs:
            defs.append('ESP')
    elif mnemonic == 'SAR' or mnemonic == 'SAL':
        if 'eflags' not in defs:
            defs.append('eflags')
    elif mnemonic == 'SETNZ':
        if 'eflags' not in uses:
            uses.append('eflags')
    elif mnemonic == 'SHR' or mnemonic == 'SHL':
        if 'eflags' not in defs:
            defs.append('eflags')
    elif mnemonic == 'STOSD.REP':
        defs = []
        defs.append('[EDI]')
        defs.append('EDI')
        uses.append('EAX')
        uses.append('EDI')
        uses.append('eflags')
    elif mnemonic == 'TEST':
        if 'eflags' not in defs:
            defs.append('eflags')
    else:
        return

    # Generate and return the define-use label without handling 'CALL'
    def_use_label = "D: {} U: {}".format(", ".join(sorted(defs)), ", ".join(sorted(uses)))
    instruction_def_use[addr_str] = {"def": defs, "use": uses}
    return def_use_label, defs, uses


def is_in_eflags(register):
    EFLAGS = {"CF", "PF", "AF", "ZF", "SF", "OF", "DF", "TF", "IF", "IOPL", "NT", "RF", "VM", "AC", "VIF", "VIP", "ID"}
    return register in EFLAGS


def collect_instructions(func):
    global addresses_count
    global instructions_count

    instruction_list = []
    jumps = {}  # Maps source to destination addresses for jumps
    conditional_jumps = set()  # Addresses of conditional jumps
    ret_instructions = set()  # Addresses of return instructions
    def_use_info = {}  # Maps addresses to define-use information
    storage = DDStorage()
    dependsOn = {}  # Maps address to dependency information
    # Initialize the basic block model and task monitor
    basicBlockModel = BasicBlockModel(currentProgram)
    monitor = ConsoleTaskMonitor()
    addrSet = func.getBody()
    codeBlockIter = basicBlockModel.getCodeBlocksContaining(addrSet, monitor)

    # Iterate through blocks and instructions to collect information
    while codeBlockIter.hasNext():
        codeBlock = codeBlockIter.next()
        addressIterator = codeBlock.getAddresses(True)
        for addr in addressIterator:
            addresses_count += 1
            instruction = getInstructionAt(addr)
            if instruction:
                instructions_count += 1
                addr_str = addr.toString()[2:]  # Extract address without "0x"
                instruction_list.append(addr_str)

                def_use_label, defs, uses = analyze_instruction(instruction, addr_str)
                def_use_info[addr_str] = def_use_label

                depend = storage.processDataDep(uses,defs,addr_str)
                dependsOn[addr_str] = depend

                # Check if the current instruction is a 'RET' instruction. If so, add its address to the "ret_instructions" set.
                if instruction.getMnemonicString() == 'RET':
                    ret_instructions.add(addr_str)

                # Record jump instructions
                if instruction.getFlowType().isJump() and instruction.getFlows():
                    dst_addr = instruction.getFlows()[0].toString()[2:]  # Extract address without "0x"
                    jumps[addr_str] = dst_addr
                    # Determine if the jump is conditional
                    if instruction.getFlowType().isConditional():
                        conditional_jumps.add(addr_str)

    instruction_list.sort(key=lambda x: int(x, 16))  # Sort instructions by address

    print("ret: ", ret_instructions)
    return [instruction_list, jumps, conditional_jumps, ret_instructions, def_use_info, dependsOn]


def get_function_entry_block(func, basicBlockModel, monitor):
    """
    Retrieves the entry block for the function.
    
    :param func: The function to get the entry block for.
    :param basicBlockModel: The basic block model used for block analysis.
    :param monitor: The task monitor.
    :return: The entry block of the function.
    """
    entryBlock = basicBlockModel.getCodeBlockAt(func.getEntryPoint(), monitor)
    return entryBlock


def find_ret_blocks(func):
    ret_blocks = set()
    basicBlockModel = BasicBlockModel(currentProgram)
    monitor = ConsoleTaskMonitor()
    addrSet = func.getBody()
    codeBlockIter = basicBlockModel.getCodeBlocksContaining(addrSet, monitor)

    while codeBlockIter.hasNext():
        codeBlock = codeBlockIter.next()
        addressIterator = codeBlock.getAddresses(True)
        for addr in addressIterator:
            instruction = getInstructionAt(addr)
            if instruction and instruction.getMnemonicString() == 'RET':
                ret_blocks.add(codeBlock)
                break

    return list(ret_blocks)


def path_to_instructions(path):
    instructions = []
    for block in path:
        # Get the minimum and maximum addresses for the block
        minAddress = block.getMinAddress()
        maxAddress = block.getMaxAddress()

        # Create an instruction iterator for the block's address range
        instructionIterator = currentProgram.getListing().getInstructions(minAddress, True)

        while instructionIterator.hasNext():
            instr = instructionIterator.next()

            # Append the instruction to the list if it's within the block's range
            if instr.getMinAddress().compareTo(maxAddress) <= 0:
                instructions.append(instr)
            else:
                # If the instruction address exceeds the block's max address, stop processing this block
                break
    print("===")
    print("||ins:", instructions)
    return instructions


def display_paths(paths):
    for path in paths:
        print(path)
        print()
    print("The length of paths is {}".format(len(paths)))


def traverse(block, visited, path, paths, entry_block, loop_limit=1):
    if visited.get(block, 0) >= loop_limit:
        return
    visited[block] = visited.get(block, 0) + 1
    new_path = [block] + path
    if block == entry_block:
        paths.append(new_path)
        return
    sources_iterator = block.getSources(monitor)
    while sources_iterator.hasNext():
        source_block = sources_iterator.next().getSourceBlock()
        traverse(source_block, visited.copy(), new_path, paths, entry_block, loop_limit)


def reverse_traverse_cfg(func, ret_blocks, basicBlockModel, monitor):
    def traverse(block, visited, path, paths, entry_block, loop_limit=1):
        """
        Recursively traverse the CFG in reverse, starting from a given block.
        
        :param block: The current block to process.
        :param visited: A dictionary tracking the visit count for each block.
        :param path: The current accumulation of blocks in the path.
        :param paths: A list of all paths discovered.
        :param entry_block: The entry block of the function.
        :param loop_limit: The maximum number of times a block can be visited to prevent infinite loops.
        """
        # Check if the current block has reached the loop limit
        if visited.get(block, 0) == loop_limit:
            return

        # Update visitation count
        visited[block] = visited.get(block, 0) + 1

        # Prepend the current block to the path
        new_path = [block] + path

        # If we've reached the entry block, save the path and return
        if block == entry_block:
            paths.append(new_path)
            return

        # Recursively visit the predecessors of the current block
        sources_iterator = block.getSources(monitor)
        has_predecessors = False
        while sources_iterator.hasNext():
            has_predecessors = True
            source_block = sources_iterator.next().getSourceBlock()
            traverse(source_block, visited.copy(), new_path, paths, entry_block)

        # If the block has no predecessors, it's a potential entry path, save it
        if not has_predecessors:
            paths.append(new_path)

    # Retrieve the entry block of the function
    entry_block = get_function_entry_block(func, basicBlockModel, monitor)

    paths = []
    visited = {block: 0 for block in basicBlockModel.getCodeBlocksContaining(func.getBody(), monitor)}
    for ret_block in ret_blocks:
        traverse(ret_block, visited, [], paths, entry_block)

    # display_paths(paths)

    all_instructions = []
    for path in paths:
        path_instructions = path_to_instructions(path)
        all_instructions.append(path_instructions)

    print("length: ", len(all_instructions))
    return all_instructions


def process_functions():
    global functions_count
    final_result = ""
    function_manager = currentProgram.getFunctionManager()
    functions = function_manager.getFunctions(True)

    for func in functions:
        # if func.getName() == "FUN_004019eb":
        #if func.getName() != "FUN_00401406":
        if func.getName() == "FUN_00401078":
            basicBlockModel = BasicBlockModel(currentProgram)
            monitor = ConsoleTaskMonitor()
            functions_count += 1
            instruction_list, jumps, conditional_jumps, ret_instructions, def_use_info, dependsOn = collect_instructions(func)
            dot_graph = create_dot_graph_DD(func, instruction_list, jumps, conditional_jumps, ret_instructions, dependsOn)
            print(dot_graph)
            #print("debug: ", dependsOn['40101c'])
            dot_graph_UD = create_dot_graph(func, instruction_list, jumps, conditional_jumps, ret_instructions,def_use_info)
            print(dot_graph_UD)
            final_result += dot_graph + "\n\n"

            ret_blocks = find_ret_blocks(func)
            print("ret_blocks: {}".format(ret_blocks))

            reverse_traverse_cfg(func, ret_blocks, basicBlockModel, monitor)
        #break

    return final_result





def main():
    process_functions()
    """
    try:
        final_result = process_functions()
        print("{} functions, {} addresses, {} instructions processed.".format(functions_count, addresses_count,
                                                                              instructions_count))
        # Define the file path to the Desktop directory
        desktop_path = os.path.join(os.path.expanduser("~"), "Desktop")
        file_path = os.path.join(desktop_path, "submission.dot")

        # Attempt to write content to the file
        with open(file_path, "w") as file:
            file.write(final_result)
        print("submission.dot created.")
        print(instruction_def_use)

    except Exception as e:
        raise Exception("Failed to create submission.dot. Error: {}".format(e))
    """


if __name__ == '__main__':
    main()
