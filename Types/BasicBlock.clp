;Copyright (c) 2012, Joshua Scoggins 
;All rights reserved.
;
;Redistribution and use in source and binary forms, with or without
;modification, are permitted provided that the following conditions are met:
;    * Redistributions of source code must retain the above copyright
;      notice, this list of conditions and the following disclaimer.
;    * Redistributions in binary form must reproduce the above copyright
;      notice, this list of conditions and the following disclaimer in the
;      documentation and/or other materials provided with the distribution.
;    * Neither the name of Joshua Scoggins nor the
;      names of its contributors may be used to endorse or promote products
;      derived from this software without specific prior written permission.
;
;THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
;ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
;WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
;DISCLAIMED. IN NO EVENT SHALL Joshua Scoggins BE LIABLE FOR ANY
;DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
;(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
;LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
;ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
;------------------------------------------------------------------------------
; BasicBlock.clp - A CLIPS wrapper for the LLVM type
(defclass BasicBlock (is-a Diplomat LLVMValue List)
 (multislot UnlinkedInstructions (visibility public))
 (multislot Predecessors)
 (multislot Successors)
 (multislot ProducingBlocks)
 (multislot ConsumingBlocks))
 ;(multislot InvariantOperands)
 ;(multislot VariantOperands))
 
(defmessage-handler BasicBlock .IsSplitBlock () 
 "Checks to see if this block is a split block. Meaning it has more than one
 successor"
 (> (length ?self:Successors) 1))

(defmessage-handler BasicBlock .IsJoinBlock () 
 "Checks to see if this block is a join block. Meaning it has more than one
 predecessor"
 (> (length ?self:Predecessors) 1))

(defmessage-handler BasicBlock .AddPredecessor (?p)
 (bind ?self:Predecessors (create$ ?self:Predecessors ?p)))

(defmessage-handler BasicBlock .AddPredecessors ($?p)
 (bind ?self:Predecessors (create$ ?self:Predecessors ?p)))

(defmessage-handler BasicBlock .AddSuccessor (?p)
 (bind ?self:Successors (create$ ?self:Successors ?p)))

(defmessage-handler BasicBlock .AddSuccessors ($?p)
 (bind ?self:Successors (create$ ?self:Successors ?p)))
