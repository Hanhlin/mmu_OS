#include <fstream>
#include <iostream>
#include <getopt.h>
#include <string.h>
#include <stdio.h>
#include <cstring>
#include <vector>
#include <deque>
#include <cmath>
#include <cctype>
#include <climits>

using namespace std;

#define NOOP
#define MAX_VPAGES 64                  //max nunmber of page table entry
#define MAX_FRAMES 128                 //max nunmber of physical page frames
#define R_COST 1
#define W_COST 1
#define C_COST 130
#define E_COST 1250
#define MAPS 300
#define UNMAPS 400
#define INS 3100
#define OUTS 2700
#define FINS 2800
#define FOUTS 2400
#define ZEROS 140
#define SEGV 340
#define SEGPROT 420

int frameNum;                               //number of frames defined by argv
int ranNum;                                 //total number of random number
int vpage;
int instNum = -1;
bool O_flag = false;
bool P_flag = false;
bool F_flag = false;
bool S_flag = false;
char inBuffer[1048576];
char rBuffer[1048576];
char operation;

struct Inst {
    char oper;
    int vpage;
};

struct VMA {
    int start_vpage;
    int end_vpage;
    int write_protected;
    int file_mapped;
};

//32 bits
struct pte_t {
    unsigned int PRESENT:1;
    unsigned int REFERENCED:1;
    unsigned int MODIFIED:1;
    unsigned int PAGEOUT:1;
    unsigned int PHY_FRAME:7;               //index of frame table
    unsigned int CHECKED:1;                 //whether the vpage has been checked if it is part of one of VMAs
    unsigned int ACCESSED:1;                //whether the vpage is part of one of VMAs
    unsigned int FILE_MAPPED:1;
    unsigned int WRITE_PROTECT:1;
};

struct frame_t {
    int frame_ind;
    unsigned int MAPPED:1;
    unsigned int PROC:4;
    unsigned int VPAGE:6;
    unsigned int AGE:32;
    unsigned int TIMELASTUSE:20;
};

struct pstats {
    int unmaps = 0;
    int maps = 0;
    int ins = 0;
    int outs = 0;
    int fins = 0;
    int fouts = 0;
    int zeros = 0;
    int segv = 0;
    int segprot = 0;
    int read = 0;
    int write = 0;
    int exit = 0;
    int ctx_switch = 0;
};

class Process {
    public:        
        //Constructor: initialize all bits with 0
        Process() { memset(page_table, 0, MAX_VPAGES*sizeof(pte_t)); }
        int pid;    
        vector<VMA> vmas;                   //virtual memory areas
        pte_t page_table[MAX_VPAGES];
        pstats proc_states;   
};

Process *current_process;
frame_t frame_table[MAX_FRAMES];
deque<int> free_list;
vector<int> randvals;
vector<Process*> pro_ptr;
vector<Inst> insts;

class Pager {
    public:
        //virtual base class
        virtual frame_t* select_victim_frame() = 0;
        virtual void reset_age(int ind) = 0;
};
Pager *THE_PAGER;

class FIFO: public Pager {
    private:
        int ind = 0;
    public:
        void reset_age(int ind) { NOOP; }
        frame_t* select_victim_frame() {
            if (ind >= frameNum) ind = 0;
            return &frame_table[ind++]; 
        }
};

class RANDOM: public Pager {
    private:
        int rofs = -1;
        int myrandom() {
            if (++rofs >= ranNum) rofs = 0;
            return (randvals[rofs] % frameNum);
        }
    public:
        void reset_age(int ind) { NOOP; }
        frame_t* select_victim_frame() {
            return &frame_table[myrandom()];
        }
};

class CLOCK: public Pager {
    private:
        int frame_ind = -1;
    public:
        void reset_age(int ind) { NOOP; }
        frame_t* select_victim_frame() {           
            while (true) {
                if (++frame_ind >= frameNum) frame_ind = 0;
                int pro = frame_table[frame_ind].PROC;
                int vpage = frame_table[frame_ind].VPAGE;
                pte_t* pt = &pro_ptr[pro]->page_table[vpage];
                if (!pt->REFERENCED) {
                    return &frame_table[frame_ind];
                }
                else {
                    pt->REFERENCED = 0;
                }
            }
        }
};

class ESC: public Pager {
    private:
        int last_reset = 0;
        int frame_ind = 0;
        int victim_ind = 0;
        bool reset = false;
        void reset_rbit() {
            reset = false;
            for (int i = 0; i < frameNum; i++) {
                frame_t* ft = &frame_table[i];
                pro_ptr[ft->PROC]->page_table[ft->VPAGE].REFERENCED = 0;
            }
        }
    public:
        void reset_age(int ind) { NOOP; }

        frame_t* select_victim_frame() {
            if (instNum - last_reset + 1 >= 50) {
                reset = true;
                last_reset = instNum + 1;
            }
            int scan = 0;
            int lowest_class = 4;
            while (scan < frameNum) {
                if (frame_ind >= frameNum) frame_ind = 0;
                int pro = frame_table[frame_ind].PROC;
                int vpage = frame_table[frame_ind].VPAGE;
                pte_t* pt = &pro_ptr[pro]->page_table[vpage];

                int current_class = 2 * pt->REFERENCED + pt->MODIFIED;
                if (current_class == 0) {
                    victim_ind = frame_ind;
                    break;
                }
                else 
                if (current_class < lowest_class) {
                    lowest_class = current_class;
                    victim_ind = frame_ind;
                }
                scan++;
                frame_ind++;
            }
            if (reset) reset_rbit();
            frame_t* ft = &frame_table[victim_ind];
            frame_ind = victim_ind + 1;
            return ft;
        }
};

class AGING: public Pager {
    private:
        unsigned int min:32;
        int frame_ind = 0;
        int victim_ind = 0;
    public:
        void reset_age(int ind) {
            frame_table[ind].AGE = 0;
        }
        
        frame_t* select_victim_frame() {
            //update age
            for (int i = 0; i < frameNum; i++) {
                frame_table[i].AGE = frame_table[i].AGE >> 1;
                if (pro_ptr[frame_table[i].PROC]->page_table[frame_table[i].VPAGE].REFERENCED) {
                    frame_table[i].AGE = frame_table[i].AGE | 0x80000000;
                    pro_ptr[frame_table[i].PROC]->page_table[frame_table[i].VPAGE].REFERENCED = 0;
                }
            }
            //choose the least referenced
            min = UINT_MAX;
            int frames_scanned = 0;
            while (frames_scanned < frameNum) {
                if (frame_ind >= frameNum) frame_ind = 0;
                if (frame_table[frame_ind].AGE < min) {
                    min = frame_table[frame_ind].AGE;
                    victim_ind = frame_ind;
                }
                frame_ind++;
                frames_scanned++;
            }
            frame_ind = victim_ind + 1;
            return &frame_table[victim_ind];
        }
};

class WORKING: public Pager {
    private:
        int TAU = 49;
        int frame_ind = 0;
        int victim_ind = 0;
        int oldest_used;
    public:
        void reset_age(int ind) { NOOP; }
        frame_t* select_victim_frame() {
            int frames_scanned = 0;
            oldest_used = INT_MAX;
            while (frames_scanned < frameNum) {
                if (frame_ind >= frameNum) frame_ind = 0;
                pte_t* pt = &pro_ptr[frame_table[frame_ind].PROC]->page_table[frame_table[frame_ind].VPAGE];
                if (pt->REFERENCED) {
                    pt->REFERENCED = 0;
                    frame_table[frame_ind].TIMELASTUSE = instNum;
                }
                else {
                    if (instNum - frame_table[frame_ind].TIMELASTUSE <= TAU) {
                        if (oldest_used > frame_table[frame_ind].TIMELASTUSE) {
                            oldest_used = frame_table[frame_ind].TIMELASTUSE;
                            victim_ind = frame_ind;
                        }
                    }
                    else {
                        frame_t* ft = &frame_table[frame_ind];
                        frame_ind++;
                        return ft;
                    }
                }
                frame_ind++;
                frames_scanned++;
            }
            frame_ind = victim_ind + 1;
            return &frame_table[victim_ind];
        }
};

frame_t* allocate_frame_from_free_list() {
    if (free_list.size() == 0) return NULL;
    int ind = free_list.front();
    free_list.pop_front();
    frame_t *frame = &frame_table[ind];
    frame->frame_ind = ind;
    return frame;
}

frame_t* get_frame() {
    frame_t *frame = allocate_frame_from_free_list();
    if (frame == nullptr) {
        frame = THE_PAGER->select_victim_frame();
    }
    return frame;
}

bool get_next_instruction(char* operation_add, int* vpage_add) {
    if (insts.empty()) return false;
    *operation_add = insts.front().oper;
    *vpage_add = insts.front().vpage;
    insts.erase(insts.begin());
    return true;
}

bool pagefault_handler(pte_t *pte, int vpage) {
    //determine whether the vpage can be accessed
    if (!pte->CHECKED) {
        pte->CHECKED = 1;
        vector<VMA> vma = current_process->vmas;
        for (auto v = vma.begin(); v != vma.end(); v++) {
            if (v->start_vpage <= vpage && v->end_vpage >= vpage) {
                pte->FILE_MAPPED = v->file_mapped;  
                pte->WRITE_PROTECT = v->write_protected;
                pte->ACCESSED = 1;
            }
        }
    }
    
    if (!pte->ACCESSED) {
        printf(" SEGV\n");
        current_process->proc_states.segv++;
        if (operation == 'w') current_process->proc_states.write++;
        else current_process->proc_states.read++;
        return true;
    }
    // else {
    frame_t *newframe = get_frame();
    int old_proc = newframe->PROC;
    int old_vpage = newframe->VPAGE;
    pte_t *pte_old = &pro_ptr[old_proc]->page_table[old_vpage];

    if (newframe->MAPPED) {
        /*** UNMAP ***/
        pte_old->PRESENT = 0;
        newframe->MAPPED = 0;
        printf(" UNMAP %d:%d\n", old_proc, old_vpage);
        pro_ptr[old_proc]->proc_states.unmaps++;

        //*** CHECK MODIFIED ***/
        if (pte_old->MODIFIED) {
            if (pte_old->FILE_MAPPED) {
                printf(" FOUT\n");
                pro_ptr[old_proc]->proc_states.fouts++;
            }
            else {
                printf(" OUT\n");
                pro_ptr[old_proc]->proc_states.outs++;
                pte_old->PAGEOUT = 1;
            }
            pte_old->MODIFIED = 0;
        }
    }

    /*** CHECK PAGEOUT ***/
    if (pte->PAGEOUT) {
        printf(" IN\n");
        current_process->proc_states.ins++;
    }
    else if (pte->FILE_MAPPED) {
        printf(" FIN\n");
        current_process->proc_states.fins++;
    }
    else {
        printf(" ZERO\n");
        current_process->proc_states.zeros++;
    }

    /*** MAP ***/
    printf(" MAP %d\n", newframe->frame_ind);
    THE_PAGER->reset_age(newframe->frame_ind);
    newframe->MAPPED = 1;
    newframe->PROC = current_process->pid;
    newframe->VPAGE = vpage;
    pte->PRESENT = 1;
    current_process->page_table[vpage].PHY_FRAME = newframe->frame_ind;
    current_process->proc_states.maps++;
    // }
    return false;
}

void update_pte(pte_t *pte, char operation) {
    switch (operation) {
    case 'w':
        if (pte->WRITE_PROTECT) {
            pte->REFERENCED = 1;
            printf(" SEGPROT\n");
            current_process->proc_states.segprot++;
        }
        else {
            pte->REFERENCED = 1;
            pte->MODIFIED = 1;
        }
        current_process->proc_states.write++;
        break;
    
    case 'r':
        pte->REFERENCED = 1;
        current_process->proc_states.read++;
        break;
    }
}

void print_page_table() {
    int proN = 0;
    for (auto it = pro_ptr.begin(); it != pro_ptr.end(); it++) {
        printf("PT[%d]:",proN++);
        for (int i = 0; i < MAX_VPAGES; i++) {
            pte_t pt = (*it)->page_table[i];
            if (!pt.PRESENT && !pt.PAGEOUT) printf(" *");
            else if (!pt.PRESENT && pt.PAGEOUT) printf(" #");
            else {
                printf(" %d:%s%s%s", i, (pt.REFERENCED)?"R":"-", (pt.MODIFIED)?"M":"-", (pt.PAGEOUT)?"S":"-");
            }
        }
        printf("\n");
    }
}

void Simulation() {
    while (get_next_instruction(&operation, &vpage)) {
        instNum++;
        printf("%d: ==> %c %d\n", instNum, operation, vpage);
        
        // handle special case of “c” and “e” instruction 
        if (operation == 'c') {
            current_process = pro_ptr[vpage];
            current_process->proc_states.ctx_switch++;
            continue;
        }
        if (operation == 'e') {
            //if (O_flag) 
            printf("EXIT current process %d\n", current_process->pid);
            for (int i = 0; i < 64; i++) {
                pte_t pt = current_process->page_table[i];
                if (pt.PRESENT) {
                    printf(" UNMAP %d:%d\n", current_process->pid, i);
                    frame_table[pt.PHY_FRAME].MAPPED = 0;
                    free_list.push_back(pt.PHY_FRAME);
                    current_process->proc_states.unmaps++;
                    if (pt.FILE_MAPPED && pt.MODIFIED) {
                        printf(" FOUT\n");
                        current_process->proc_states.fouts++;
                    }
                }
            }

            memset(current_process->page_table, 0, MAX_VPAGES*sizeof(pte_t));
            current_process->proc_states.exit++;
            continue;
        }

        // now the real instructions for read and write 
        pte_t *pte = &current_process->page_table[vpage]; 
        if (!pte->PRESENT) {
            bool segv = pagefault_handler(pte, vpage);
            if (segv) continue;
        }
        update_pte(pte, operation);
    }
}

void read_line(ifstream& inFile) {
    do {
        inFile.getline(inBuffer, 1048576);
    } while (inBuffer[0] == '#');
}

void print_frame_table() {
    printf("FT:");
    for (int i = 0; i < frameNum; i++) {
        if (frame_table[i].MAPPED == 0) printf(" *");
        else printf(" %d:%d", frame_table[i].PROC, frame_table[i].VPAGE);
    }
    printf("\n");
}

void print_statistics() {
    int proN = 0;
    int ctx_switches = 0;
    int pro_exits = 0;
    int read_num = 0;
    int write_num = 0;
    int map_num = 0;
    int unmap_num = 0;
    int in_num = 0;
    int out_num = 0;
    int fin_num = 0;
    int fout_num = 0;
    int zero_num = 0;
    int segv_num = 0;
    int segprot_num = 0;
    int64_t total_cost = 0;

    for (auto it = pro_ptr.begin(); it != pro_ptr.end(); it++) {
        pstats ps = (*it)->proc_states;
        ctx_switches += ps.ctx_switch;
        pro_exits += ps.exit;
        read_num += ps.read;
        write_num += ps.write;
        map_num += ps.maps;
        unmap_num += ps.unmaps;
        in_num += ps.ins;
        out_num += ps.outs;
        fin_num += ps.fins;
        fout_num += ps.fouts;
        zero_num += ps.zeros;
        segv_num += ps.segv;
        segprot_num += ps.segprot;
        printf("PROC[%d]: U=%d M=%d I=%d O=%d FI=%d FO=%d Z=%d SV=%d SP=%d\n",
                proN, ps.unmaps, ps.maps, ps.ins, ps.outs, ps.fins, ps.fouts, ps.zeros, ps.segv, ps.segprot);
        proN++;
    }

    total_cost += R_COST*read_num;
    total_cost += W_COST*write_num;
    total_cost += C_COST*ctx_switches;
    total_cost += E_COST*pro_exits;
    total_cost += MAPS*map_num;
    total_cost += UNMAPS*unmap_num;
    total_cost += INS*in_num;
    total_cost += OUTS*out_num;
    total_cost += FINS*fin_num;
    total_cost += FOUTS*fout_num;
    total_cost += ZEROS*zero_num;
    total_cost += SEGV*segv_num;
    total_cost += SEGPROT*segprot_num;
    printf("TOTALCOST %d %d %d %lld %lu\n", instNum+1, ctx_switches, pro_exits, total_cost, sizeof(pte_t));
}

int main(int argc, char* argv[]) {    
    int arg;
    char algo;
    setbuf(stdout, NULL);
    
    while ((arg = getopt(argc, argv, "f:a:o:")) != -1) {
        switch (arg) {
        case 'f':
            frameNum = atoi(optarg);
            for (int i = 0; i < frameNum; i++) {
                free_list.push_back(i);
            }
            break;
        
        case 'a':
            //Page Replacement Algorithm
            algo = *optarg;
            switch (toupper(algo)) {
            case 'F':
                THE_PAGER = new FIFO();
                break;
            case 'R':
                THE_PAGER = new RANDOM();
                break;
            case 'C':
                THE_PAGER = new CLOCK();
                break;
            case 'E':
                THE_PAGER = new ESC();
                break;
            case 'A':
                THE_PAGER = new AGING();
                break;
            case 'W':
                THE_PAGER = new WORKING();
                break;
            }
            break;
        
        case 'o':
            //Option arguments
            for(char* it = optarg; *it; ++it) {
                switch (*it) {
                case 'O':
                    O_flag = true;
                    break;
                case 'P':
                    P_flag = true;
                    break;
                case 'F':
                    F_flag = true;
                    break;
                case 'S':
                    S_flag = true;
                    break;
                };
            }
            break;
        }
    }

    #pragma region read rFile into a vector
    bool Skip = true;
    ifstream rFile(argv[optind+1]);
    while (rFile.getline(rBuffer, 1048576)) {
        int random;
        if (Skip) {
            random = stoi(rBuffer);
            ranNum = random;
            Skip = false;
            continue;
        }

        random = stoi(rBuffer);
        randvals.push_back(random);
    }
    #pragma endregion read rFile into a vector

    #pragma region read inputfile into process pointer vector
    ifstream inFile(argv[optind]);
    int ProNum = 0, i = 0;
    int SP, EP, WP, FM, VMAs;
    VMA vma;

    read_line(inFile);
    ProNum = atoi(inBuffer);
    for (int i = 0; i < ProNum; i++) {
        Process* pro = new Process();
        pro->pid = i;
        read_line(inFile);
        VMAs = atoi(inBuffer);
        for (int j = 0; j < VMAs; j++) {
            read_line(inFile);
            sscanf(inBuffer, "%d %d %d %d", &SP, &EP, &WP, &FM);
            vma = { SP, EP, WP, FM };
            pro->vmas.push_back(vma);
        }
        pro_ptr.push_back(pro);
    }

    //read Instructions
    char oper;
    int vpage;
    Inst inst;
    while (!inFile.eof()) {
        read_line(inFile);
        if (!inFile.eof()) {
            sscanf(inBuffer, "%c %d", &oper, &vpage);
            inst = { oper, vpage };
            insts.push_back(inst);
        }
    }
    #pragma endregion read inputfile into process vector/ process pointer queue, and create event
    
    Simulation();
    
    if (P_flag) print_page_table();
    if (F_flag) print_frame_table();
    if (S_flag) print_statistics();
}