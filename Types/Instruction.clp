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
;------------------------------------------------------------------------------
; Instruction.clp - Base LLVM Instruction class
; Written by Joshua Scoggins
;------------------------------------------------------------------------------

(defclass Instruction (is-a LLVMUser InteropObject)
 (slot NumSuccessors)
 (slot HasValueHandle (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsDereferenceablePointer (type SYMBOL) (allowed-values FALSE TRUE))
 (slot MayWriteToMemory (type SYMBOL) (allowed-values FALSE TRUE)) 
 (slot MayReadFromMemory (type SYMBOL) (allowed-values FALSE TRUE))
 (slot MayReadOrWriteMemory (type SYMBOL) (allowed-values FALSE TRUE))
 (slot MayHaveSideEffects (type SYMBOL) (allowed-values FALSE TRUE))
 (slot HasCallDependency (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsBinaryOp (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsTerminator (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsShift (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsCast (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsArithmeticShift (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsLogicalShift (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsAssociative (type SYMBOL) (allowed-values FALSE TRUE))
 (slot IsCommutative (type SYMBOL) (allowed-values FALSE TRUE))
 (slot Predicate (type SYMBOL))
 (slot Operation (type SYMBOL))
 (slot TimeIndex (type NUMBER) (default-dynamic 0))
 ;(slot ExecutionLength (type NUMBER) (default-dynamic -1))
 (slot MemoryTarget (type SYMBOL) (default-dynamic nil))
 (multislot LocalDependencies)
 (multislot NonLocalDependencies)
 (multislot Consumers)
 (multislot Producers)
 (multislot DestinationRegisters)
 (multislot SourceRegisters (visibility public)))
 ;(multislot BlocksUsedIn (visibility public)))
 ;(slot InstructionType (type SYMBOL) (default-dynamic nil)))
;------------------------------------------------------------------------------
(defmessage-handler Instruction init after ()
 ;copy the Operands into SourceRegisters and Producers list
 ;this should save a ton of time... :D
 (bind ?self:SourceRegisters ?self:Operands)
 (bind ?self:Producers ?self:Operands))
;------------------------------------------------------------------------------
(defmessage-handler Instruction .IncrementTimeIndex ()
 (bind ?self:TimeIndex (+ 1 ?self:TimeIndex)))
;------------------------------------------------------------------------------
(defmessage-handler Instruction .DecrementTimeIndex ()
 (bind ?self:TimeIndex (- ?self:TimeIndex 1)))
;------------------------------------------------------------------------------
