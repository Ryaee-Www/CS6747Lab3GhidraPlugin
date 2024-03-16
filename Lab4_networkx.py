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
    return create_dot_graph(func, instruction_list, jumps, conditional_jumps, ret_instructions, def_use_info)


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


def display_paths(paths):
    print()
    for path in paths:
        print(path)
        print()
    print("The length of paths is {}".format(len(paths)))


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

    # Cycle detection and handling
    #cycles = list(nx.simple_cycles(cfg))
    #for cycle in cycles:
        # Simple cycle breaking: remove one edge per cycle
        #cfg.remove_edge(cycle[-1], cycle[0])  # Removes the edge leading back to the cycle's start

    # Find paths from entry block to each of the return blocks
    all_paths = []
    for ret_block in ret_blocks:
        for path in nx.all_simple_paths(cfg, source=entry_block, target=ret_block):
            all_paths.append(path)

    # Extract instructions from the paths
    # Assuming a function `path_to_instructions` exists
    all_paths_instructions = [path_to_instructions(path) for path in all_paths]

    # Additional processing or display
    # Assuming functions `display_paths` and `prepend_START_to_each_path` exist
    display_paths(all_paths_instructions)
    prepended_paths = prepend_START_to_each_path(all_paths_instructions)
    display_paths(prepended_paths)

    return prepended_paths


def process_functions():
    global functions_count
    final_result = ""
    function_manager = currentProgram.getFunctionManager()
    functions = function_manager.getFunctions(True)

    for func in functions:
        if func.getName() == "FUN_004019eb":
        #if func.getName() == "FUN_00401406":
        #if func.getName() == "FUN_00402292":
            functions_count += 1
            dot_graph = collect_instructions(func)
            print(dot_graph)
            final_result += dot_graph + "\n\n"
            
            ret_blocks = find_ret_blocks(func)
            #print("ret_blocks: {}".format(ret_blocks))

            all_instructions = reverse_traverse_cfg(func, ret_blocks)

    return final_result, all_instructions

class DDStorage:
    # A custom data structure used to manage and track data dependencies in a set of instructions.
    def __init__(self):
        # Initialize storage containers for registers, pointers, flags, and a stack
        self.registers = {}  # Maps registers to their most recent defining instruction
        self.pointers = {}   # Maps pointers to lists of their defining instructions
        self.flags = {}      # Maps flags to their most recent defining instruction
        self.stack = []  # Tracks stack operations (PUSH/POP) with their instructions

    def update_register(self, instr, register, address):
        # Update the register with the instruction and address
        self.registers[register] = (instr, address)

    def update_pointer(self, instr, pointer, address):
        # If the pointer doesn't exist, initialize it as a list
        if pointer not in self.pointers:
            self.pointers[pointer] = []
        # Append the instruction and address to the pointer's list
        self.pointers[pointer].append((instr, address))

    def update_flag(self, instr, flag, address):
        # Update the flag with the instruction and address
        self.flags[flag] = (instr, address)

    def push_stack(self, instr, address):
        # Push an instruction and its address onto the stack
        self.stack.append((instr, address))

    def pop_stack(self):
        # Pop the top instruction from the stack if it's not empty
        if self.stack:
            return self.stack.pop()
        return None

class DDStorage:
    def __init__(self):
        self.registers = {}
        self.pointers = {}
        self.flags = {}
        self.stack = []

    def update_register(self, register, instr_address):
        self.registers[register] = instr_address

    def update_pointer(self, pointer, instr_address):
        if pointer not in self.pointers:
            self.pointers[pointer] = []
        self.pointers[pointer].append(instr_address)

    def update_flag(self, flag, instr_address):
        self.flags[flag] = instr_address

    def pop_stack(self):
        return self.stack.pop() if self.stack else None

    def push_stack(self, instr_address):
        self.stack.append(instr_address)

    def find_dependencies(self, use):
        dependencies = []
        if use in self.registers:
            dependencies.append(self.registers[use])
        if use in self.pointers:
            dependencies.extend(self.pointers[use])
        if use in self.flags:
            dependencies.append(self.flags[use])
        return dependencies

def compute_data_dependencies(all_paths, instruction_def_use):
    all_dependencies = {}

    for path_index, path in enumerate(all_paths):
        dd_storage = DDStorage()  # Initialize a new DDStorage object for each path
        definitions = {}  # Maps variables to their defining instruction address for direct dependencies

        for instr_index, instr in enumerate(path):
            if instr == "START":
                continue  # Skip processing for START instruction as it has no dependencies

            dependencies = []

            if instr in instruction_def_use:
                defs, uses = instruction_def_use[instr]['def'], instruction_def_use[instr]['use']
            else:
                defs, uses = [], []

            # Determine the instruction address
            instr_address = instr.getAddress().toString()  # This line assumes you have a way to get the address

            # Identify dependencies using addresses
            for use in uses:
                dep_addresses = dd_storage.find_dependencies(use)
                dependencies.extend(dep_addresses)

            # Update DDStorage with new definitions using addresses
            for def_item in defs:
                if def_item.startswith('[') and def_item.endswith(']'):
                    dd_storage.update_pointer(def_item, instr_address)
                else:
                    dd_storage.update_register(def_item, instr_address)

            instr_key = (instr_address, instr)  # Use instruction's address and instruction as key
            all_dependencies[instr_key] = {
                'def': defs,
                'use': uses,
                'DD': dependencies,  # Now storing addresses of dependencies
            }

    return all_dependencies


def generate_DD_dot_graph():
    pass


def main():

    try:
        final_result, all_paths = process_functions()
        DD_dot_graph = generate_DD_dot_graph()
        print("{} functions, {} addresses, {} instructions processed.".format(functions_count, addresses_count,
                                                                              instructions_count))
        # Define the file path to the Desktop directory
        desktop_path = os.path.join(os.path.expanduser("~"), "Desktop")
        file_path = os.path.join(desktop_path, "submission.dot")

        # Attempt to write content to the file
        with open(file_path, "w") as file:
            file.write(final_result)
        print("submission.dot created.")
        
        all_dependencies = compute_data_dependencies(all_paths, instruction_def_use)
        
        print("all_dependencies:")
        print(all_dependencies)

        print()
        for key, value in all_dependencies.items():
            print(key)
            print(value)
            print()

    except Exception as e:
        raise Exception("Failed to create submission.dot. Error: {}".format(e))
        
if __name__ == '__main__':
    main()
