//
//  main.cpp
//  prakKK
//
//  Created by Анна on 04/12/2019.
//  Copyright © 2019 Анна. All rights reserved.
//

#define export exports
extern "C" {
    #include "qbe/all.h"
}
#undef export

#include <iostream>
#include <unordered_set>
#include <unordered_map>
#include <string>
#include <stack>
#include <vector>

class SSA {
    std::unordered_map<uint, std::unordered_set<uint>> Blocks; // Variable(val, Blocks={...})
    std::unordered_set<uint> Globals;
    std::unordered_map<uint, Blk*> BlockNames;
    std::unordered_map<uint, std::unordered_set<uint>> BlockDF;
    std::unordered_map<uint, std::unordered_set<uint>> DominatorsTree;
    std::unordered_map<uint, std::unordered_map<uint, std::vector<std::pair<uint, int>>>> BlockPhiFuncs;
    std::unordered_map<uint, std::stack<int>> Stacks;
    std::unordered_map<uint, int> Counters;
public:
    void fillGlobalsAndBlocks(Fn *fn) {
        for (Blk *blk = fn->start; blk; blk = blk->link){
            //names
            BlockNames.emplace(blk->id, blk);
            //DF
            std::unordered_set<uint> df;
            for (auto i = 0; i < blk->nfron; i++) {
                df.insert((blk->fron)[i]->id);
            }
            BlockDF.emplace(blk->id, std::forward<std::unordered_set<uint>>(df));
            //DominatorsTree
            if (blk->idom != nullptr) {
                if (DominatorsTree.find(blk->idom->id) == DominatorsTree.end()) {
                    std::unordered_set<uint> b = {blk->id};
                    DominatorsTree.emplace(blk->idom->id, std::forward<std::unordered_set<uint>>(b));
                }
                else DominatorsTree[blk->idom->id].insert(blk->id);
            }
            //Globals and Blocks
            if (blk->nins) {
                for (auto i=blk->ins; (i - blk->ins) < blk->nins; i++) {
                    if (rtype(i->to) == RTmp) {
                        Globals.insert(i->to.val);
                        if (Blocks.find(i->to.val) == Blocks.end()) {
                            std::unordered_set<uint> blcks = {blk->id};
                            Blocks.emplace(static_cast<const uint> (i->to.val), std::forward<std::unordered_set<uint>>(blcks));
                        }
                        else {
                            Blocks[i->to.val].insert(blk->id);
                        }
                    }
                    if (rtype(i->arg[0]) == RTmp) Globals.insert(i->arg[0].val);
                    if (rtype(i->arg[1]) == RTmp) Globals.insert(i->arg[1].val);
                }
            }
        }
    }
    void addPhiFuncs (Fn *fn) {
        std::unordered_set<uint> WorkList;
        for (auto var : Globals) {
            std::unordered_set<uint> Processed_blocks;
            WorkList = Blocks[var];
            while (WorkList.size() != 0) {
                for (auto blck : WorkList) {
                    Processed_blocks.insert(blck);
                    for (auto df : BlockDF[blck]) {
                        addPhi(var, df);
                        WorkList.insert(df);
                    }
                }
                for (auto blck : Processed_blocks)
                    if (WorkList.find(blck) != WorkList.end()) WorkList.erase(blck);
            }
        }
    }
    
    void addPhi (uint var, uint blck) {
        if (BlockPhiFuncs.find(blck) == BlockPhiFuncs.end()) {
            std::pair<uint,int> p = {0,-10};
            std::vector<std::pair<uint,int>> vp = {p};
            std::unordered_map<uint, std::vector<std::pair<uint,int>>> phi;
            phi.emplace(var, std::forward<std::vector<std::pair<uint,int>>>(vp));
            BlockPhiFuncs.emplace(blck, std::forward<std::unordered_map<uint, std::vector<std::pair<uint,int>>>>(phi));
        }
        else {
            if (BlockPhiFuncs[blck].find(var) == BlockPhiFuncs[blck].end()) {
                std::pair<uint,int> p = {0,-10};
                std::vector<std::pair<uint,int>> vp = {p};
                BlockPhiFuncs[blck].emplace(var, std::forward<std::vector<std::pair<uint,int>>>(vp));
            }
        }
    }
    
    void setPhiNum (Fn *fn) {
        for (auto var : Globals) {
            std::stack<int> st; st.push(-1);
            Stacks.emplace(var, std::forward<std::stack<int>>(st));
            Counters.emplace(var, 0);
        }
        Rename(fn, fn->start);
    }
    
    int NewName(uint var) {
        int i = Counters[var];
        Counters[var]++;
        Stacks[var].push(i);
        return i;
    }
    
    void fillPhiParams(uint block_id, uint succ_block_id) {
        if (BlockPhiFuncs.find(succ_block_id) != BlockPhiFuncs.end()) {
            auto PhiFuncs = BlockPhiFuncs[succ_block_id];
            for (auto& it_phi_func : BlockPhiFuncs[succ_block_id]) {
                std::pair<uint,int> p = {block_id,Stacks[it_phi_func.first].top()};
                it_phi_func.second.push_back(p);
            }
        }
    }
    
    void Rename(Fn *fn, Blk* block) {
        //1
        for (auto& it_phi_func : BlockPhiFuncs[block->id]) {
            it_phi_func.second[0].second = NewName(it_phi_func.first);
        }
        //2
        for (auto i=block->ins; (i - block->ins) < block->nins; i++) {
            if (rtype(i->to) == RTmp) {
                if (Globals.find(i->to.val) != Globals.end()) {
                    NewName(i->to.val);
                }
            }
        }
        //3
        if (block->s1 != nullptr) {
            //std::cout << "BLOCK :: " << block->name << " | SUCC :: " << block->s1->name << std::endl;
            fillPhiParams(block->id, block->s1->id);
            //printContext(fn);
            //std::cout << std::endl;
        }
        if (block->s2 != nullptr) {
            //std::cout << "BLOCK :: " << block->name << " | SUCC :: " << block->s1->name << std::endl;
            fillPhiParams(block->id, block->s2->id);
            //printContext(fn);
            //std::cout << std::endl;
        }
        //4
        if (DominatorsTree.find(block->id) != DominatorsTree.end()) {
            for (auto succ : DominatorsTree[block->id]) {
                Rename(fn, BlockNames[succ]);
            }
        }
        //5
        for (auto& it_phi_func : BlockPhiFuncs[block->id]) {
            Stacks[it_phi_func.first].pop();
        }
        //6
        for (auto i=block->ins; (i - block->ins) < block->nins; i++) {
            if (rtype(i->to) == RTmp) {
                if (Globals.find(i->to.val) != Globals.end()) {
                    Stacks[i->to.val].pop();
                }
            }
        }
    }
    
    
    void printContext (Fn *fn) {
        //Blocks(x)
        /*for (auto it : Blocks) {
            std::cout << "var: " << fn->tmp[it.first].name << " | Blocks={";
            for (auto& blck : it.second) {
                std::cout << BlockNames[blck]->name << ", ";
            }
            std::cout << "}" << std::endl;
        }
        
        //Globals
        std::cout << "\nGlobals: ";
        for (auto it : Globals) {
            std::cout << fn->tmp[it].name << ", ";
        }
        std::cout << std::endl;
        
        //Block Names
        std::cout << "\nBlocks: \n";
        for (auto blck : BlockDF) {
            std::cout << "   " << BlockNames[blck.first]->name << ": DF={";
            for (auto df : blck.second) {
                std::cout << BlockNames[df]->name << ",";
            }
            std::cout<<"}\n";
        }
        //PhiFuncs
        std::cout << "\nBlocks: \n";
        for (auto blck : BlockPhiFuncs) {
            std::cout << "   " << BlockNames[blck.first]->name << ": Phi={";
            for (auto phi : blck.second) {
                std::cout << fn->tmp[phi.first].name << "[" << phi.second[0].second << "]=(@" << BlockNames[phi.second[1].first]->name << " " << phi.second[1].second << ",@" << BlockNames[phi.second[2].first]->name << " "  << phi.second[2].second << "), ";
            }
            std::cout<<"}\n";
        }*/
        //DominatorTree
        std::cout << "\nDominatorsTree: \n";
        for (auto blck : DominatorsTree) {
            std::cout << BlockNames[blck.first]->name << ": ";
            for (auto dom_suc : blck.second) {
                std::cout << BlockNames[dom_suc]->name << ", ";
            }
            std::cout << std::endl;
        }
        //Stacks
        /*std::cout << "\nStacks: \n";
        for (auto it_st : Stacks) {
            std::cout << "   " << fn->tmp[it_st.first].name << "_index_" << it_st.second.top() << std::endl;
        }
        std::cout << "\nCounters: \n";
        for (auto it_st : Counters) {
            std::cout << "   " << fn->tmp[it_st.first].name << "_count_" << it_st.second << std::endl;
        }
        */
        std::cout << "\nDF: \n";
        for (auto blck : BlockDF) {
            std::cout << BlockNames[blck.first]->name << ": ";
            for (auto fron : blck.second) {
                std::cout << BlockNames[fron]->name << ", ";
            }
            std::cout << std::endl;
        }
    }
    
    void printOutput(Fn *fn) {
        for (Blk *blk = fn->start; blk; blk = blk->link){
            std::cout << "@" << blk->name << ":\n";
            if (BlockPhiFuncs.find(blk->id) != BlockPhiFuncs.end()) {
                for (auto phi_it : BlockPhiFuncs[blk->id]) {
                    std::cout << "    %" << fn->tmp[phi_it.first].name << " " << phi_it.second[0].second << " = @";
                    if (phi_it.second.size() > 0) {
                        auto it_phi_args = phi_it.second.begin() + 1;
                        while (((it_phi_args) != phi_it.second.end()) && ((it_phi_args + 1) != phi_it.second.end())) {
                            std::cout << BlockNames[it_phi_args->first]->name << " " << it_phi_args->second << "  @";
                            it_phi_args++;
                        }
                        if (it_phi_args!= (phi_it.second.begin() + 1))
                            std::cout << BlockNames[it_phi_args->first]->name << " " << it_phi_args->second << std::endl;
                    }
                 }
            }
        }
    }
    
} ssaObj;


static void readfn (Fn *fn) {
    fillrpo(fn);
    filldom(fn);
    fillfron(fn);
    ssaObj.fillGlobalsAndBlocks(fn);
    ssaObj.addPhiFuncs(fn);
    ssaObj.setPhiNum(fn);
    ssaObj.printContext(fn);
}

static void readdat (Dat *dat) {
    (void) dat;
}

int main () {
    char str [] = "<stdin>";
    parse(stdin, str, readdat, readfn);
    freeall();
}
