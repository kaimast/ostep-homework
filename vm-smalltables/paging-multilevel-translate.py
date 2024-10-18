#! /usr/bin/env python3

''' Simulates a simple multi (two) level page table '''

#pylint: disable=too-many-branches,too-many-instance-attributes,invalid-name,too-many-public-methods,too-many-locals

from optparse import OptionParser
import random

def to_bits(num, count, shift=0):
    ''' Convert the number to a bit string '''

    assert num <= pow(2,count)
    assert shift >= 0

    absolute = shift + count
    result = ""
    for offset in reversed(range(count)):
        bit = (num >> offset) & 1
        result += str(bit)
        absolute -= 1
        if absolute > 0 and absolute % 4 == 0:
            result += ' '

    return result

def generate_bitmask(num_bits, shift=0):
    ''' Creates a bitmask of n bits set to 1 that can be shifted '''
    res = 0
    for idx in range(num_bits):
        res |= 1 << (idx + shift)
    return res

class OS:
    ''' The memory management logic '''

    def __init__(self):
        # 128 byte pages
        self.page_bits         = 5
        self.page_size         = pow(2, self.page_bits)

        # 4k phys memory (128 pages)
        self.num_phys_pages    = 128
        self.phys_mem_size     = self.page_size * self.num_phys_pages
        self.vpn_size          = 10
        self.num_virtual_pages = pow(2, self.vpn_size)
        self.virt_mem_size     = self.page_size * self.num_virtual_pages
        self.pte_size          = 1

        # Data that the OS tracks
        self.used_pages       = []
        self.used_pages_count = 0
        self.max_page_count   = int(self.phys_mem_size / self.page_size)

        # no pages used (yet)
        self.used_pages= [0 for _ in range(0, self.max_page_count)]

        # set contents of memory to 0, too
        self.memory = [0 for _ in range(0, self.phys_mem_size)]

        # associative array of pdbr's (indexed by PID)
        self.pdbr = {}

        self.pte_shift = self.page_bits
        self.pte_bits  = 5
        self.pte_mask  = generate_bitmask(self.pte_bits, shift=self.pte_shift)

        self.pde_shift = self.pte_shift+self.pte_bits
        self.pde_bits  = self.vpn_size - self.pte_bits
        self.pde_mask  = generate_bitmask(self.pde_bits, shift=self.pde_shift)

        self.vpn_mask  = self.pde_mask | self.pte_mask
        self.vpn_shift = self.pte_shift

        self.offset_mask = generate_bitmask(self.page_bits)

        self.vaddr_len = self.pde_bits + self.pte_bits + self.page_bits

    def print_bits(self, addr):
        ''' Prints every bit of an address '''

        pde = (addr & self.pde_mask) >> self.pde_shift
        pde_str = to_bits(pde, self.pde_bits, shift=self.pde_shift)

        pte = (addr & self.pte_mask) >> self.pte_shift
        pte_str = to_bits(pte, self.pte_bits, shift=self.pte_shift)

        offset = addr & self.offset_mask
        offset_str = to_bits(offset, self.page_bits)

        padding = "   "

        print(padding +  f"        Bits: |{pde_str}|{pte_str}|{offset_str}|")

        hexvals = padding+" Hexadecimal: |"
        for (value, bitstr) in [(pde, pde_str), (pte, pte_str), (offset, offset_str)]:
            nbits = len(bitstr)
            hexval = f'{value:x}'
            assert len(hexval) <= len(bitstr)

            if len(hexval)+2 <= len(bitstr):
                hexval = '0x'+hexval

            hexvals += ' ' * (nbits - len(hexval)) + hexval + '|'
        print(hexvals)

        decvals = padding+"     Decimal: |"
        for (value, bitstr) in [(pde, pde_str), (pte, pte_str), (offset, offset_str)]:
            nbits = len(bitstr)
            decval = str(value)
            assert len(decval) <= len(bitstr)
            decvals += ' ' * (nbits - len(decval)) + decval + '|'
        print(decvals)

        labels  = padding+"              |"
        for (name, bits) in [("PDE", pde_str), ("PTE", pte_str), ("offset", offset_str)]:
            nbits = len(bits) # The lengths fo the string rep, not the number of actual bits
            if len(name) <= nbits:
                label = name + ' ' * (nbits - len(name))
            else:
                label = name[:nbits]

            labels += label + '|'

        print(labels)
        print('')

    def find_free(self):
        ''' Finds an unused page and marks it as in use '''

        assert self.used_pages_count < self.max_page_count
        look = int(random.random() * self.max_page_count)
        while self.used_pages[look] == 1:
            look = int(random.random() * self.max_page_count)
        self.used_pages_count = self.used_pages_count + 1
        self.used_pages[look] = 1
        return look

    def init_page_directory(self, which_page):
        ''' Fills page directory with invalid entires '''
        which_byte = which_page << self.page_bits
        for idx in range(which_byte, which_byte + self.page_size):
            self.memory[idx] = 0x7f

    def init_pagetable_page(self, which_page):
        ''' Fills pagetable pagey with invalid entires '''
        self.init_page_directory(which_page)

    def get_pte_bits(self, virtual_addr):
        ''' Get the offset within the page table page for an address '''
        return (virtual_addr & self.pte_mask) >> self.pte_shift

    def get_pagetable_entry(self, virtual_addr, pte_page, print_stuff=False):
        ''' Get contents of a specific PTE '''

        pte_bits = self.get_pte_bits(virtual_addr)
        pte_addr = (pte_page << self.page_bits) | pte_bits
        pte     = self.memory[pte_addr]
        valid   = (pte & 0x80) >> 7
        pfn     = pte & 0x7f

        if print_stuff is True:
            print(f'    --> PTE contents:0x{pte:x} '
                  f'(valid {valid}, PFN 0x{pfn:02x} [decimal {pfn}])')

        return (valid, pfn, pte_addr)

    def print_page_directory(self, pid, highlight=None):
        ''' Show contents of the page directory for the specified process '''

        page_dir = self.pdbr[pid]
        num_entries = pow(2, self.pde_bits)

        if highlight:
            assert highlight >= 0
            assert highlight < num_entries

        print("# Page Directory")
        for idx in range(num_entries):
            pde_addr = (page_dir << self.page_bits) | idx
            pde      = self.memory[pde_addr]
            valid    = (pde & 0x80) >> 7
            pt_ptr   = pde & 0x7f

            line = f'{idx:002}: '

            if valid:
                line += f'0x{pt_ptr:02x} [decimal {pt_ptr}]'
            else:
                line += '- invalid - '

            if highlight and idx == highlight:
                print(f'* {line} *')
            else:
                print(f'  {line}  ')

    def print_pagetable_page(self, pte_page, highlight=None):
        ''' Print the contents of a page a of the page table '''

        num_entries = pow(2, self.pte_bits)

        if highlight:
            assert highlight >= 0
            assert highlight < num_entries

        print(f"# Pagetable @ {pte_page}")
        for idx in range(num_entries):
            _pte, valid, pfn = self.get_pagetable_entry(pte_page, idx)

            line = f'{idx:002}: '

            if valid:
                line += f'0x{pfn:02x} [decimal {pfn}]'
            else:
                line += '- invalid -'

            if highlight and idx == highlight:
                print(f'* {line} *')
            else:
                print(f'  {line}  ')

    def walk(self, vaddr):
        ''' Prints the page table path for an address '''

        (valid, pt_ptr, _) = self.get_pagedir_entry(1, vaddr)
        pdir_idx = self.get_pde_bits(vaddr)
        self.print_page_directory(1, highlight=pdir_idx)

        if valid:
            print('')
            (valid, pfn, _) = self.get_pagetable_entry(vaddr, pt_ptr)
            pte_bits = self.get_pte_bits(vaddr)
            self.print_pagetable_page(pdir_idx, highlight=pte_bits)

        if valid:
            print('')
            offset = vaddr & self.offset_mask
            self.print_physical_page(pfn, highlight=offset)
        print('')

    def fetch_physical_page(self, page_num):
        ''' Get the contents of a physical page '''

        start = page_num*self.page_size
        assert start < len(self.memory)

        return self.memory[start:start+self.page_size]

    def memory_dump(self):
        ''' Show content of the entire physical memory '''
        for page_num in range(int(self.phys_mem_size / self.page_size)):
            content = [f'{value:02x}' for value in self.fetch_physical_page(page_num)]
            print(f'Page {page_num:3d}: '+' '.join(content))

    def print_physical_page(self, pfn, highlight=None):
        ''' Print the contents physical page '''

        print(f"# Phyiscal Page @ {pfn}")

        content = [f'{value:02x}' for value in self.fetch_physical_page(pfn)]
        print(''.join(content))

        if highlight:
            assert highlight >= 0
            assert highlight < self.page_size
            print(f"{' ' * 2 * highlight}^^")

    def get_pde_bits(self, virtual_addr):
        ''' Get the offset within the PDE for an address '''
        return (virtual_addr & self.pde_mask) >> self.pde_shift

    def get_pagedir_entry(self, pid, virtual_addr, print_stuff=False):
        ''' Get the page directory entry corresponding to the virtual address '''

        page_dir  = self.pdbr[pid]
        pde_bits  = self.get_pde_bits(virtual_addr)
        pde_addr = (page_dir << self.page_bits) | pde_bits
        pde      = self.memory[pde_addr]
        valid    = (pde & 0x80) >> 7
        pt_ptr   = pde & 0x7f

        if print_stuff is True:
            print(f'  --> PDE contents: Ox{pde:x} '
                  f'(valid {valid}, pfn 0x{pt_ptr:02x} [decimal {pt_ptr}]')
        return (valid, pt_ptr, pde_addr)

    def set_pagetable_entry(self, pte_addr, physicalPage):
        ''' Store a new page table entry '''
        self.memory[pte_addr] = 0x80 | physicalPage

    def set_pagedir_entry(self, pde_addr, physicalPage):
        ''' Store a new page directory entry '''
        self.memory[pde_addr] = 0x80 | physicalPage

    def alloc_virtual_page(self, pid, virtualPage, physicalPage):
        ''' Map a page the in the process' memory to a physical page '''

        # make it into a virtual address, as everything uses this (and not VPN)
        virtual_addr = virtualPage << self.page_bits
        (valid, pt_ptr, pde_addr) = self.get_pagedir_entry(pid, virtual_addr, False)
        if valid == 0:
            # must allocate a page of the page table now, and have the PD point to it
            assert pt_ptr == 127
            pte_page = self.find_free()
            self.set_pagedir_entry(pde_addr, pte_page)
            self.init_pagetable_page(pte_page)
        else:
            # otherwise, just extract page number of page table page
            pte_page = pt_ptr
        # now, look up page table entry too, and mark it valid and fill in translation
        (valid, pfn, pte_addr) = self.get_pagetable_entry(virtual_addr, pte_page, False)
        assert valid == 0
        assert pfn == 127
        self.set_pagetable_entry(pte_addr, physicalPage)

    def translate(self, pid, virtual_addr):
        '''
        Converts a virtual adddres into a physical address 
        Returns -2 on PTE fault and -1 on PDE fault
        '''
        (valid, pt_ptr, _pde_addr) = self.get_pagedir_entry(pid, virtual_addr, True)
        if valid == 1:
            pte_page = pt_ptr
            (valid, pfn, _pte_addr) = self.get_pagetable_entry(virtual_addr, pte_page, True)
            if valid == 1:
                offset = virtual_addr & self.offset_mask
                paddr  = (pfn << self.page_bits) | offset
        		# print('     --> pfn: %02x  offset: %x' % (pfn, offset))
                return paddr

            return -2
        return -1

    def fill_page(self, which_page):
        ''' Fill a phyiscal page with random data '''

        for j in range(0, self.page_size):
            self.memory[(which_page * self.page_size) + j] = int(random.random() * 31)

    def allocate_process(self, pid, numPages):
        ''' Set up the virutal memory for a process '''

        # need a PDBR: find one somewhere in memory
        pageDir = self.find_free()
        # print('**ALLOCATE** page dir', pageDir)
        self.pdbr[pid] = pageDir
        self.init_page_directory(pageDir)

        used = {}
        for vp in range(0, self.num_virtual_pages):
            used[vp] = 0
        allocatedVPs = []

        for vp in range(0, numPages):
            vp = int(random.random() * self.num_virtual_pages)
            while used[vp] == 1:
                vp = int(random.random() * self.num_virtual_pages)
            assert used[vp] == 0
            used[vp] = 1
            allocatedVPs.append(vp)
            pp = self.find_free()
            # print('**ALLOCATE** page', pp)
            # print('  trying to map vp:%08x to pp:%08x' % (vp, pp))
            self.alloc_virtual_page(pid, vp, pp)
            self.fill_page(pp)
        return allocatedVPs

    def get_pdbr(self, pid):
        ''' Get the page directory base register for the specified process '''
        return self.pdbr[pid]

    def get_value(self, addr):
        ''' Return the data at the specified memory location'''
        return self.memory[addr]

# allocate some processes in memory
# allocate some multi-level page tables in memory
# make a bit of a mystery:
# can examine PDBR (PFN of current proc's page directory)
# can examine contents of any page
# fill pages with values too
# ask: when given
#   LOAD VA, R1
# what will final value will be loaded into R1?

def main():
    ''' The main logic of the script '''
    parser = OptionParser()
    parser.add_option('-s', '--seed', default=0, help='the random seed',
                      action='store', type='int', dest='seed')
    parser.add_option('-a', '--allocated', default=64, help='number of virtual pages allocated',
                      action='store', type='int', dest='allocated')
    parser.add_option('-n', '--addresses', default=10, action='store', type='int', dest='num',
                      help='number of virtual addresses to generate')
    parser.add_option('-c', '--solve', help='compute answers for me',
                      action='store_true', default=False, dest='solve')
    parser.add_option('-b', '--show_bits', action='store_true', default=False, dest='show_bits',
                      help='Display how the each address breakds down into its components')
    parser.add_option('--walk', help='Show the PDE and PTE for each address',
                      action='store_true', default=False, dest='walk')
    parser.add_option('--show-page-directory', help='Show all entries of page directory',
                      action='store_true', default=False, dest='show_page_dir')
    parser.add_option('--show-page-table', action='store', type=int, default=None,
                      dest='show_page_table',
                      help='Show contents of pagatable page with the specified PFN')
    parser.add_option('--show-physical-page', action='store', type=int, default=None,
                      dest='show_physical_page',
                      help='Show contents of a physical page with the specified PFN')


    (options, _args) = parser.parse_args()

    print('ARG seed', options.seed)
    print('ARG allocated',  options.allocated)
    print('ARG num',  options.num)
    print('')

    random.seed(options.seed, version=1)

    # do the work now
    os = OS()
    used = os.allocate_process(1, options.allocated)

    if options.show_page_dir:
        os.print_page_directory(1)
        return

    if options.show_page_table:
        os.print_pagetable_page(options.show_page_table)
        return

    if options.show_physical_page:
        os.print_physical_page(options.show_physical_page)
        return


    os.memory_dump()

    print('')
    print(f'PDBR: {os.get_pdbr(1)} (decimal) '
           '[This means the page directory is held in this page]')
    print('')

    for i in range(0, options.num):
        if (random.random() * 100) > 50.0 or i >= len(used):
            vaddr = int(random.random() * 1024 * 32)
        else:
            vaddr = (used[i] << 5) | int(random.random() * 32)

        print(f'Virtual Address: 0x{vaddr:04x}')

        if options.walk:
            os.walk(vaddr)

        if options.show_bits or options.solve:
            os.print_bits(vaddr)

        if options.solve:
            r = os.translate(1, vaddr)
            if r > -1:
                print(f'      --> Translates to Physical Address 0x{r:03x} '
                      f'--> Value: 0x{os.get_value(r):02x}')
            elif r == -1:
                print('      --> Fault (page directory entry not valid)')
            else:
                print('      --> Fault (page table entry not valid)')
            print(' ')

if __name__ == "__main__":
    main()
