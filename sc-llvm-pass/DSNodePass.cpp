//===- DSNodePass.cpp: - --------------------------------------------------===//
// 
//                          The SAFECode Compiler 
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
// 
//===----------------------------------------------------------------------===//
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "dsnode"

#include <iostream>
#include <signal.h>
#include <vector>
#include <set> 
#include <sstream>

#include "llvm/LLVMContext.h"
#include "llvm/Module.h" 
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Type.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Assembly/Writer.h"

#include "safecode/Config/config.h"
#include "safecode/SAFECodeConfig.h"

#include "poolalloc/PoolAllocate.h"
#include "dsa/DSNode.h"
#include "dsa/DSSupport.h"

namespace llvm {

/// Passes that holds DSNode and Pool Handle information
struct DSNodePass : public ModulePass {
public :
  static char ID;
  DSNodePass () : ModulePass (ID) { }
  const char *getPassName() const {
    return "DS Node And Pool Allocation Handle Pass";
  }
  virtual bool runOnModule(Module &M);
  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    getAnalysisUsageForPoolAllocation(AU);
    AU.setPreservesAll();
  };
  
  // Get analysis usage for DSA. Make sure all SAFECode passes have the same
  // dependency on DSA.
  static void getAnalysisUsageForDSA(AnalysisUsage &AU);
  
  // Get analysis usage for Pool Allocation. It is a hack to lie to the
  // PassManager to make sure Pool Allocation only run only one time.
  // This function tells the PassManager it preseves DSA and PoolAllocation
  // results, which is clearly a lie.
  static void getAnalysisUsageForPoolAllocation(AnalysisUsage &AU);
  
  static void preservePAandDSA(AnalysisUsage &AU);
  
  // FIXME: Provide better interfaces
  PoolAllocate * paPass;
  DSGraph * getDSGraph (Function & F);
  DSNode* getDSNode(const Value *V, Function *F);
  
  void dumpPoolType(DSNode *dsn, Value *pool);
  void dumpPoolConn(std::set<Value*> & poolCycle, DSNode *dsn, Function & F, 
		    PoolAllocate *paPass);
  void dumpPoolTypeShallow(DSNode *dsn, Value *pool);
  void dumpPoolConnShallow(std::set<Value*> & poolMemo, DSNode *dsn, Function & F, PoolAllocate *paPass);
  void buildPoolConn(Module & M, PoolAllocate *paPass);
		  
  //
  // Try to find the DSNode for the global variable
  //
  DSNode * getDSNodeForGlobalVariable(const GlobalValue * GV);
  unsigned getDSNodeOffset(const Value *V, Function *F);
};
  
char DSNodePass::ID = 0; 
static RegisterPass<DSNodePass>
passDSNode("ds-node", "Sample Region Fetching Code", true, true);
  
cl::opt<bool> CheckEveryGEPUse("check-every-gep-use", cl::init(true),
			       cl::desc("Check every use of GEP"));
  
void DSNodePass::dumpPoolConn(std::set<Value*> & poolCycle, DSNode *dsn, Function & F, 
			      PoolAllocate *paPass) {  
  for (DSNode::edge_iterator E = dsn->edge_begin(), Ee = dsn->edge_end(); E != Ee; ++E) {
    DSNode *head = E->second.getNode();
    if (head) {
      Value *pool = paPass->getPool(head, F);

      // Currently infix traversal!?
      errs() << pool->getName().str();
      if (E != dsn->edge_begin()) {
	errs() << ", ";
      }
      
      // Check for cycles. 
      if (poolCycle.find(pool) == poolCycle.end()) {
	poolCycle.insert(pool);
	dumpPoolConn(poolCycle, head, F, paPass);
      }
    }
    errs() << "\n";
  }
}

void DSNodePass::dumpPoolType(DSNode *dsn, Value *pool) {
  errs() << pool->getName().str() << "<";

  // We iterate over the types at struct offsets. 
  for (DSNode::type_iterator T = dsn->type_begin(), Te = dsn->type_end(); 
       T != Te; ++T) {
    // unsigned idx = T->first;
    // Each offset contains a set of possible types. 
    SuperSet<Type*>::setPtr types = T->second;
    
    // Print out the DS node's type information.
    errs() << "(";
    for (svset<Type*>::const_iterator TY = types->begin(), TYe = types->end(); 
	 TY != TYe; ++TY) {
      Type * const t = *TY;
      t->dump();
      if (TY + 1 != TYe) {
	errs() << ", ";
      }
    }
    errs() << ")";
  }

  errs() << ">\n";
}

void DSNodePass::dumpPoolTypeShallow(DSNode *dsn, Value *pool) {
  errs() << pool->getName().str() << "<";

  if (dsn->isNodeCompletelyFolded()) {
    errs() << "i8>:"; 
    return;
  }
  else if (dsn->isUnknownNode()) {
    errs() << "i8>:";
    return;
  }
  else if (dsn->type_begin() == dsn->type_end()) {
    errs() << "i8>:"; 
    return;
  }
  else {
    errs() << "i64>:";
    return; 
  }

  /*
  // We iterate over the types at struct offsets. 
  for (DSNode::type_iterator T = dsn->type_begin(), Te = dsn->type_end(); 
       T != Te; ++T) {
    unsigned idx = T->first;
    // Each offset contains a set of possible types. 
     SuperSet<Type*>::setPtr types = T->second;
    
    // Print out the DS node's type information.
    for (svset<Type*>::const_iterator TY = types->begin(), TYe = types->end(); 
	 TY != TYe; ++TY) {
      Type * const t = *TY;
      t->dump();
      errs() << " ";
      break; 
    }
  }
  */

  errs() << ">:";
}

void DSNodePass::dumpPoolConnShallow(std::set<Value*> & poolMemo, DSNode *dsn, Function & F, PoolAllocate *paPass) {  
  for (DSNode::edge_iterator E = dsn->edge_begin(), Ee = dsn->edge_end(); E != Ee; ++E) {
    DSNode *head = E->second.getNode();
    if (head) {
      Value *pool = paPass->getPool(head, F);

      if (pool) {
	if (E != dsn->edge_begin()) {
	  errs() << ", ";
	}
	errs() << pool->getName().str();
      }
    }
  }
  errs() << "#\n";

  for (DSNode::edge_iterator E = dsn->edge_begin(), Ee = dsn->edge_end(); E != Ee; ++E) {
    DSNode *head = E->second.getNode();
    if (head) {
      Value *pool = paPass->getPool(head, F);

      if (pool) {
	if (poolMemo.find(pool) == poolMemo.end()) {
	  poolMemo.insert(pool);
	  dumpPoolTypeShallow(head, pool);
	  dumpPoolConnShallow(poolMemo, head, F, paPass);
	}
      }
    }
  }
}

void DSNodePass::buildPoolConn(Module & M, PoolAllocate *paPass) {
  // This keeps track of which pools we have already seen.
  std::set<Value*> poolMemo;

  // This maps a pool to its full type (all the pools it transitively points into).
  std::map<Value*, std::list<Value*> > poolType;

  // This is used to detect cycles as we trace pool connectivity. 
  std::set<Value*> poolCycle; 

  // Iterate over all instructions and trace all pools. 
  for (Module::iterator F = M.begin(), Fe = M.end(); F != Fe; ++F) {
    poolMemo.clear(); 
    errs() << F->getName() << " ";

    // Dump out the return type pool by iterating over all instructions until we 
    // find a return instruction. 
    if (inst_begin(F) == inst_end(F)) {
      errs() << "(NA)"; 
    }
    else { 
      int found = 0; 
      for (inst_iterator I = inst_begin(F), Ie = inst_end(F); I != Ie; ++I) {
	if (ReturnInst* retI = dyn_cast<ReturnInst>(&*I)) {
	  if (I->getNumOperands() == 1) {
	    Value *v = I->getOperand(0);
	    Value *pool = paPass->getPoolHandle(v, F);
	    if (pool) {
	      errs() << "(" << pool->getName().str() << ")";
	    }
	    else {
	      errs() << "(NA)";
	    }
	  }
	  else {
	    errs() << "(NA)" ; 
	  }
	  found = 1;
	  break; 
	}
      }
      if (!found) {
	errs() << "(NA)" ; 
      }
    }

    // Dump out argument pools.
    errs() << " (";
    for (Function::arg_iterator A = F->arg_begin(), Ae = F->arg_end(); A != Ae; ++A) {
      Value *pool = paPass->getPoolHandle(A, F);
      if (A != F->arg_begin()) {
	errs() << ", ";
      }
      if (pool) {
	errs() << pool->getName().str();
      }
      else {
	errs() << "NA"; 
      }
    }
    errs() << ") {\n"; 

    // Begin dumping out pool info for the function body.

    PA::FuncInfo *pFinfo = paPass->getFuncInfoOrClone(*F);
    if (pFinfo) {
      std::vector<const DSNode*> argNodes = pFinfo->ArgNodes;
      for (int i = 0; i < argNodes.size(); i++) {
	DSNode *dsn = (DSNode*) argNodes[i];
	Value *pool = paPass->getPool(dsn, *F); 

	if (pool) {
	  if (poolMemo.find(pool) == poolMemo.end()) {
	    poolMemo.insert(pool); 
	  
	    dumpPoolTypeShallow(dsn, pool);
	    dumpPoolConnShallow(poolMemo, dsn, *F, paPass);
	  }
	}
      }
    }

    for (inst_iterator I = inst_begin(F), Ie = inst_end(F); I != Ie; ++I) {
      Value *poolI = paPass->getPoolHandle(&*I, F);
      if (poolI) {
	if (poolMemo.find(poolI) == poolMemo.end()) {
	  poolMemo.insert(poolI);
	  DSNode *dsn = getDSNode(&*I, F);
	  dumpPoolTypeShallow(dsn, poolI);
	  dumpPoolConnShallow(poolMemo, dsn, *F, paPass);
	}
      }

      for (unsigned j = 0; j < I->getNumOperands(); j++) {
	Value *v = I->getOperand(j);
	Value *pool = paPass->getPoolHandle(v, F);
	
	//if (pool) {
	//  errs() << "HAHA: " << pool->getName().str() << "\n";
	//}

	if (pool) {
	  // If we haven't seen the pool ...
	  if (poolMemo.find(pool) == poolMemo.end()) {
	    poolMemo.insert(pool);

	    DSNode *dsn = getDSNode(v, F);
	    //dumpPoolType(dsn, pool); 
	    //poolCycle.clear();
	    //dumpPoolConn(poolCycle, dsn, *F, paPass);
	    
	    dumpPoolTypeShallow(dsn, pool);
	    dumpPoolConnShallow(poolMemo, dsn, *F, paPass);
	  }
	}
      }
    }
    errs() << "}\n"; 
  }
}

void dumpInstruction(Module & M, Function *F, Instruction *I, PoolAllocate *paPass) {
  Value *poolI = paPass->getPoolHandle(I, F);
  std::stringstream stream;
  SmallVector<StringRef, 6> tmp;
  bool debug = false;

  if (poolI) {
    // WriteAsOperand(errs(), I, false, &M);
    // errs() << ": " << poolI->getName().str() << "\n";
    stream << poolI->getName().str();
    if (debug) { errs() << poolI->getName().str(); }
    //tmp.push_back(poolI->getName().str());
  }
  else {
    stream << "NA";
    if (debug) { errs() << "NA"; }
    //tmp.push_back("NA");
  }
  if (I->getNumOperands() != 0) {
    stream << ", ";
    if (debug) { errs() << ", "; }
  }

  for (unsigned j = 0; j < I->getNumOperands(); j++) {
    Value *o = I->getOperand(j);
    Value *pool = paPass->getPoolHandle(o, F);
    
    if (pool) {
      // WriteAsOperand(errs(), o, false, &M);
      // errs() << ": " << pool->getName().str() << "\n";
      stream << pool->getName().str();
      if (debug) { errs() << pool->getName().str(); }
      //tmp.push_back(pool->getName().str());
    }
    else {
      stream << "NA";
      if (debug) { errs() << "NA"; }
      //tmp.push_back("NA");
    }
    if (j != I->getNumOperands() - 1) {
      stream << ", ";
      if (debug) { errs() << ", "; }
    }
  }  

  //SmallVector<MDNode*, 6> tmp2;
  //for (unsigned i = 0; i < tmp.size(); i++) {
  //  MDString *s = MDString::get(M.getContext(), tmp[i]);
  //  tmp2.push_back(MDNode::get(M.getContext(), ArrayRef<Value*>(s))); 
  //}
  //MDNode *N = MDNode::get(M.getContext(), tmp2.data());

  MDString *s = MDString::get(M.getContext(), stream.str());
  MDNode *N = MDNode::get(M.getContext(), ArrayRef<Value*>(s));
  I->setMetadata(M.getContext().getMDKindID("safecode"), N);

  if (debug) { errs() << "\n"; }
}

bool DSNodePass::runOnModule(Module & M) {
  paPass = &getAnalysis<PoolAllocate>();
  assert (paPass && "Pool Allocation Transform *must* be run first!");

  // Find the pool connectivity first.
  buildPoolConn(M, paPass);
  //errs() << "\n\n";

  int counter = 0;

  // Dump out the pool annotations
  for (Module::iterator F = M.begin(), Fe = M.end(); F != Fe; ++F) {
    //errs() << F->getName() << " {\n";
    unsigned bbCounter = 1; 
    for (Function::iterator B = F->begin(), Be = F->end(); B != Be; ++B) {
      //errs() << "bb" << bbCounter << "\n";
      for (BasicBlock::iterator I = B->begin(), Ie = B->end(); I != Ie; ++I) {	
	// MDString s = MDString("hello world");
	std::string str = std::string("hello world");
	std::stringstream convert;   // stream used for the conversion
	convert << counter; 
	MDString *s = MDString::get(M.getContext(), str.append(convert.str()));
	ArrayRef<Value*> tmp = ArrayRef<Value*>(s);
	MDNode *N = MDNode::get(M.getContext(), tmp);
	// I->setMetadata(M.getContext().getMDKindID("safecode"), N);

	dumpInstruction(M, F, I, paPass);
	counter ++;
      }
      bbCounter++; 
      //errs() << "\n";
    }
    //errs() << "}\n";
  }

  return true;
}

  /*
void
DSNodePass::visitInstruction (Instruction & I) {
  Function * F = I.getParent()->getParent();
  for (unsigned index = 0; index < I.getNumOperands(); ++index) {
    Value * Pool = paPass->getPoolHandle (I.getOperand(index), F);
    if (Pool) {
      std::cerr << Pool->getName().str() << " : ";
    } else {
      std::cerr << "No Pool : ";
    }
    I.getOperand(index)->dump();
  }
}
  */

//
// Method: getDSGraph()
//
// Description:
//  Return the DSGraph for the given function.  This method automatically
//  selects the correct pass to query for the graph based upon whether we're
//  doing user-space or kernel analysis.
//
DSGraph *
DSNodePass::getDSGraph(Function & F) {
  return paPass->getDSGraph(F);
}

DSNode* DSNodePass::getDSNode (const Value *VOrig, Function *F) {
  //
  // If this function has a clone, then try to grab the original.
  //
  bool isClone = false;
  Value * Vnew = (Value *)(VOrig);
  if (!(paPass->getFuncInfo(*F))) {
    isClone = true;
    F = paPass->getOrigFunctionFromClone(F);
    PA::FuncInfo *FI = paPass->getFuncInfoOrClone(*F);
    if (!FI->NewToOldValueMap.empty()) {
      Vnew = FI->MapValueToOriginal (Vnew);
    }
    assert (F && "No Function Information from Pool Allocation!\n");
  }

  // Ensure that the function has a DSGraph
  assert (paPass->hasDSGraph(*F) && "No DSGraph for function!\n");

  //
  // Lookup the DSNode for the value in the function's DSGraph.
  //
  const Value * V = (Vnew) ? Vnew : VOrig;
  DSGraph * TDG = paPass->getDSGraph(*F);
  DSNode *DSN = TDG->getNodeForValue(V).getNode();

  if (DSN) {
    return DSN;
  } else if (isa<GlobalValue>(V)) {
    //
    // If the value wasn't found in the function's DSGraph, then maybe we can
    // find the value in the globals graph.
    //
    
    return getDSNodeForGlobalVariable(cast<GlobalValue>(V));
  } else {
    // Not much we can do
    return NULL;
  }

  return DSN;
}

DSNode *
DSNodePass::getDSNodeForGlobalVariable(const GlobalValue * GV) {
  DSGraph * GlobalsGraph = paPass->getGlobalsGraph ();
  DSNode * Node = GlobalsGraph->getNodeForValue(GV).getNode();
  if (Node) {
    // Fast-path
    return Node;
  } else if (isa<GlobalAlias>(GV)) {
    // DSA does not handle this...
    return NULL;
  } else {
    // We have to dig into the globalEC of the DSGraph to find the DSNode.
    const GlobalValue * V = GlobalsGraph->getGlobalECs().getLeaderValue(GV);
    return GlobalsGraph->getNodeForValue(V).getNode();
  }
}

unsigned DSNodePass::getDSNodeOffset(const Value *V, Function *F) {
  DSGraph *TDG = paPass->getDSGraph(*F);
  return TDG->getNodeForValue((Value *)V).getOffset();
}

void
DSNodePass::getAnalysisUsageForDSA(AnalysisUsage &AU) {
  AU.addRequiredTransitive<EQTDDataStructures>();
}

void
DSNodePass::getAnalysisUsageForPoolAllocation(AnalysisUsage &AU) {
  AU.addRequiredTransitive<PoolAllocate>();
  AU.addPreserved<PoolAllocate>();
  AU.addPreserved<BasicDataStructures>();
  AU.addPreserved<EQTDDataStructures>();
}

void
DSNodePass::preservePAandDSA(AnalysisUsage &AU) {
  AU.addPreserved<PoolAllocate>();
  AU.addPreserved<BasicDataStructures>();
  AU.addPreserved<EQTDDataStructures>();
}

}

llvm::Pass * createPHPass(void) {
  return new DSNodePass;
}

/*
  if (dsn->isUnknownNode()) {
    errs() << "i8>:";
  }
  else if (dsn->isAllocaNode()) {
    errs() << "alloca>:";
  }
  else if (dsn->isHeapNode()) {
    errs() << "heap>:";
  }
  else if (dsn->isGlobalNode()) {
    errs() << "global>:";
  }
  else if (dsn->isExternFuncNode()) {
    errs() << "externfunc>:"; 
  }
  else if (dsn->isModifiedNode()) {
    errs() << "modified>:";
  }
  else if (dsn->isReadNode()) {
    errs() << "read>:"; 
  }
  else if (dsn->isArrayNode()) {
    errs() << "array>:"; 
  }
  else if (dsn->isCollapsedNode()) {
    errs() << "collapsed>:"; 
  }
  else if (dsn->isIncompleteNode()) {
    errs() << "incomplete>:"; 
  }
  else if (dsn->isCompleteNode()) {
    errs() << "complete>:"; 
  }
  else if (dsn->isDeadNode()) {
    errs() << "dead>:";
  }
  else if (dsn->isExternalNode()) {
    errs() << "external>:"; 
  }
  else if (dsn->isIntToPtrNode()) {
    errs() << "inttoptr>:"; 
  }
  else if (dsn->isPtrToIntNode()) {
    errs() << "ptrtoint>:"; 
  }
  else if (dsn->isVAStartNode()) {
    errs() << "vastart>:";
  }
*/
