import sys
sys.path.append('/usr/lib/python2.7/site-packages')
sys.path.append('/usr/lib64/python2.7/site-packages/gtk-2.0')
sys.path.append('/usr/lib64/python2.7/site-packages')
sys.path.append('/home/xzhao455/.local/lib/python2.7/site-packages')
import networkx as nx
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
                #jump_style = 'conditional_jump' if addr in conditional_jumps else 'unconditional_jump'
                #dot_graph += '    {} -> {}; [{}]\n'.format(current_node, jump_to_node, jump_style)
                dot_graph += '    {} -> {};\n'.format(current_node, jump_to_node)

                # For conditional jumps, also connect to the next sequential instruction
                if addr in conditional_jumps:
                    dot_graph += '    {} -> {};\n'.format(current_node, next_node)
            elif next_node:  # Ensure sequential flow except for RET instructions
                dot_graph += '    {} -> {};\n'.format(current_node, next_node)

    dot_graph += '}'
    return dot_graph


def operandRegisterHelper(instruction, defs, uses, addr_str):
    numOperand = instruction.getNumOperands()
    for i in range(numOperand):
        operand = instruction.getRegister(i)
        opType  = instruction.getOperandRefType(i)
        
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
                        if str(element) not in uses:
                            uses.append(str(element))
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
    instruction_def_use[instruction] = {"def": defs, "use": uses}
    return def_use_label


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

                def_use_label = analyze_instruction(instruction, addr_str)
                def_use_info[addr_str] = def_use_label

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
    
    print(ret_instructions)
    return instruction_list, create_dot_graph(func, instruction_list, jumps, conditional_jumps, ret_instructions, def_use_info)


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

    return instructions


def prepend_START_to_each_path(paths):
    return [["START"] + path for path in paths]


def display_paths_length(func, paths):
    print("{}: The length of paths is {}".format(func.getName(), len(paths)))


def count_unique_instructions(all_paths_instructions):
    unique_instructions = set()
    for path_instructions in all_paths_instructions:
        for instr in path_instructions:
            unique_instructions.add(instr)
    print("Number of unique instructions: {}".format(len(unique_instructions)))


def reverse_traverse_cfg(func, ret_blocks):
    # Initialize necessary components
    basicBlockModel = BasicBlockModel(currentProgram)
    monitor = ConsoleTaskMonitor()

    # Create a directed graph to represent the CFG
    cfg = nx.DiGraph()

    entry_block = get_function_entry_block(func, basicBlockModel, monitor)

    # Populate the CFG with nodes for each block and edges to represent the control flow
    addrSet = func.getBody()
    codeBlockIter = basicBlockModel.getCodeBlocksContaining(addrSet, monitor)
    while codeBlockIter.hasNext():
        current_block = codeBlockIter.next()
        cfg.add_node(current_block)

        destIterator = current_block.getDestinations(monitor)
        while destIterator.hasNext():
            destinationReference = destIterator.next()
            successor_block = destinationReference.getDestinationBlock()
            if successor_block:
                cfg.add_edge(current_block, successor_block)

    # Modified to include depth limitation
    all_paths = []
    for ret_block in ret_blocks:
        if entry_block == ret_block:
            all_paths.append([entry_block])
        elif func.getName() == "FUN_00401406":
            max_depth = 46
            for path in nx.all_simple_paths(cfg, source=entry_block, target=ret_block, cutoff=max_depth):
                all_paths.append(path)
        else:
            for path in nx.all_simple_paths(cfg, source=entry_block, target=ret_block):
                all_paths.append(path)

    # Extract instructions from the paths
    all_paths_instructions = [path_to_instructions(path) for path in all_paths]

    # Additional processing or display
    prepended_paths = prepend_START_to_each_path(all_paths_instructions)
    display_paths_length(func, prepended_paths)
    #count_unique_instructions(all_paths_instructions)

    return prepended_paths


class DDStorage():
    def __init__(self):
        # self.uses = {}
        self.defs = {}  # Dictionary mapping register or pointer offset to its address.

    def has(self, register):
        # Check if a register or offset is defined.
        return register in self.defs

    def getAddress(self, register):
        # Retrieve the address associated with a register or offset.
        return self.defs[register]

    def newDefine(self, register, address):
        # Associate a new address with a register or offset.
        self.defs[register] = address

    def processDataDep(self, uses, defs, addr):
        """
        Processes one line of assembly code, identifying data dependencies.
        
        This should be called for each line in a basic block to accurately
        track data dependencies throughout the block.
        
        @param uses: List of 'USE', indicating registers or pointers that are read from.
        @param defs: List of 'DEF', indicating registers or pointers that are written to.
        @param addr: The address of the current assembly instruction.
        
        @return: List of addresses that the current instruction depends on. 
                 Includes "START" to indicate a dependency on initial state if necessary.
        """
        dependsOn = []
        #print("DEBUG PDD: " , addr, defs, uses)
        for i in uses:
            if self.has(i):
                dependsOn.append(self.getAddress(i))
            else:
                if 'START' not in dependsOn:
                    dependsOn.append('START')
        for i in defs:
            self.newDefine(i, addr)

        return dependsOn


def compute_data_dependencies(all_paths, instruction_def_use):
    """
    Computes data dependencies across all given paths in the assembly code.

    @param all_paths: List of all execution paths, each path is a list of instructions.
    @param instruction_def_use: Dictionary mapping instructions to their definitions ('def') and uses ('use').

    @return: Dictionary mapping instruction identifiers (address, instruction) to their dependencies ('DD'),
             definitions ('def'), and uses ('use').
    """
    # Initialize a dictionary to store dependencies for each instruction.
    all_dependencies = {}

    for path_index, path in enumerate(all_paths):
        storage = DDStorage()  # Initialize a new DDStorage object for each path


        for instr_index, instr in enumerate(path):
            if instr == "START":
                continue  # Skip processing for START instruction as it has no dependencies

            # Initialize an empty list for dependencies of the current instruction.
            dependencies = []

            instr_address = instr.getAddress().toString()

            # Check if the current instruction has defined 'def' and 'use' values.
            if instr in instruction_def_use:
                defs, uses = instruction_def_use[instr]['def'], instruction_def_use[instr]['use']
            else:
                defs, uses = [], []

            if instr.getMnemonicString() == 'RET':
                dependencies = []
            else:
                dependencies = storage.processDataDep(uses, defs, instr_address)
            instr_key = (instr_address, instr)  # Use instruction's address and instruction as key

            if instr_key in all_dependencies: # Not first entry, add to existed
                all_dependencies[instr_key] = {
                    'def': defs,
                    'use': uses,
                    'DD': list(set(all_dependencies[instr_key]['DD'] + dependencies))  # Now storing addresses of dependencies
                }
            else: # First entry
                all_dependencies[instr_key] = {
                    'def': defs,
                    'use': uses,
                    'DD': dependencies
                }

    return all_dependencies


def generate_DD_dot_graph(func, instruction_list, all_dependencies):
    entry_point = "{}".format(func.getEntryPoint().toString().lstrip('0'))
    digraph_name = "digraph 0x{}".format(entry_point)
    dot_graph = "{} {{\n".format(digraph_name)
    dot_graph += '    n0  [label = "START"];\n'
    
    address_to_node = {"START": "n0"}
    node_counter = 1
    edges = []

    instruction_list = ["00" + instr for instr in instruction_list]

    for instr in instruction_list:
        instr_address = instr
        matched_keys = [(key, deps) for key, deps in all_dependencies.items() if key[0] == instr_address]
        
        node_name = 'n{}'.format(node_counter)
        address_to_node[instr_address] = node_name
        formatted_address = instr_address.lstrip('0')

        if matched_keys:
            for instr_key, deps in matched_keys:
                dd_labels = ', '.join(['0x{}'.format(addr.lstrip('0')) if addr != 'START' else 'START' for addr in deps['DD']]) if deps['DD'] else ''
                dot_graph += '    {}  [label = "0x{}; DD: {}"];\n'.format(node_name, formatted_address, dd_labels)

                for dep_address in deps['DD']:
                    if dep_address in address_to_node:
                        dep_node = address_to_node[dep_address]
                    else:
                        dep_node = "n0"
                    edges.append((dep_address, instr_address))
        else:
            dot_graph += '    {}  [label = "0x{}; DD:"];\n'.format(node_name, formatted_address)
        
        node_counter += 1

    dot_graph += '\n'

    for dep_address, src_address in sorted(edges, key=lambda x: int(x[1], 16)):
        dep_node = address_to_node.get(dep_address, "n0")
        src_node = address_to_node[src_address]
        dot_graph += '    {} -> {};\n'.format(src_node, dep_node)

    dot_graph += '}\n'
    return dot_graph


def process_functions():
    global functions_count
    def_use_result = ""
    DD_result = ""
    basicBlockModel = BasicBlockModel(currentProgram)
    monitor = ConsoleTaskMonitor()
    function_manager = currentProgram.getFunctionManager()
    functions = function_manager.getFunctions(True)

    for func in functions:
        functions_count += 1
        instruction_list, def_use_graph = collect_instructions(func)
        #print(def_use_graph)
        def_use_result += def_use_graph + "\n\n"
            
        ret_blocks = find_ret_blocks(func)
        #print("ret_blocks: {}".format(ret_blocks))

        all_paths = reverse_traverse_cfg(func, ret_blocks)
        all_dependencies = compute_data_dependencies(all_paths, instruction_def_use)
        DD_graph = generate_DD_dot_graph(func, instruction_list, all_dependencies)
        #print(DD_graph)
        DD_result += DD_graph + "\n\n"

    return def_use_result, DD_result


def main():

    try:
        def_use_result, DD_result = process_functions()
        print("{} functions, {} addresses, {} instructions processed.".format(functions_count, addresses_count,
                                                                          instructions_count))
        # Define the file path to the Desktop directory
        desktop_path = os.path.join(os.path.expanduser("~"), "Desktop")
    
        # Paths for both files
        submission_file_path = os.path.join(desktop_path, "submission.dot")
        def_use_submission_file_path = os.path.join(desktop_path, "def_use_submission.dot")

        # Attempt to write content to the submission.dot file
        with open(submission_file_path, "w") as submission_file:
            submission_file.write(DD_result)
        print("submission.dot created.")
    
        # Attempt to write content to the def_use_submission.dot file
        with open(def_use_submission_file_path, "w") as def_use_file:
            def_use_file.write(def_use_result)
        print("def_use_submission.dot created.")

    except Exception as e:
        raise Exception("Failed to create files. Error: {}".format(e))

        
if __name__ == '__main__':
    main()
