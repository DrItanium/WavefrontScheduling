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
; BlockInvariantRegisterDetection.clp - Iterates through all of the operands of
; a given instruction and marks each operand as either being variant or
; invariant to the current block. 
;
; This is a little abstract so let's use a real example from the llvm bitcode
; representation of flops.c using LTO
; 
; In Block ._crit_edge23 there is the following instruction
;   %293 = fmul double %150, 4.000000e+00
; This instruction is actually invariant to ._crit_edge23 because one of the
; source operands is a constant (4.000000e+00) and the other operand %150 is 
; defined basic block %123 using the instruction
;   %150 = sitofp i64 %139 to double
;
; This fact means that %293 is being computed as late as possible as a way to
; reduce memory pressure with respect to spilling and filling on architectures
; such as x86. On an architecture such as ia64 this isn't such a big issue
; because there are so many registers! While I'm speculating on this I also
; believe that the late bind of the computation is to make it easier for
; superscalar processors to parallelize internally. 
;
; What's even funnier is that %150 is used again in another block
; (._crit_edge17) with the instruction:
;   %350 = fdiv double 0x40599541F7F192A4, %150
;
; While it may turn out that it's not possible to safely move %350 and %293
; into the same block as %150, it is possible to schedule them to execute
; earlier within the original block as there are no dependencies. 
; 
; The use of invariance detection also allows us to schedule instructions to be
; closer to their uses provided we are not moving into or out of a given loop.
;------------------------------------------------------------------------------
; Written by Joshua Scoggins (6/23/2012)
;------------------------------------------------------------------------------
(defrule MarkTerminatorsVariant
 (declare (salience 10))
 (Stage Analysis $?)
 ?term <- (object (is-a TerminatorInstruction) (ID ?name) (Parent ?p))
 ?bb <- (object (is-a BasicBlock) (ID ?p))
 (test (eq FALSE (member$ ?name (send ?bb get-VariantOperands))))
 =>
 (modify-instance ?term 
  (VariantOperands (send ?term get-VariantOperands) ?p))
 (modify-instance ?bb 
  (VariantOperands (send ?bb get-VariantOperands) ?name)))
;------------------------------------------------------------------------------
(defrule MarkInvariantOperand
 "Moves through a given instruction and marks all invariant operands as such"
 (Stage Analysis $?)
 ;(object (is-a Hint) (Type WavefrontSchedule) (Point Allow) (Parent ?t))
 (object (is-a Instruction) (ID ?name) (Parent ?p) (Operands $? ?target $?))
 ?bb <- (object (is-a BasicBlock) (ID ?p))
 (test (eq FALSE (member$ ?name (send ?bb get-VariantOperands))))
 (object (is-a TaggedObject) (ID ?target) (Parent ~?p))
 
 =>
 ;(printout t "Marking " ?target " as invariant to " ?p crlf)
 ;(assert (Instruction ?name dependent on ?target))
 (assert (Operand ?target invariant for Instruction ?name))
 ;this will not assert if the fact already exists :D
 (assert (Operand ?target invariant for BasicBlock ?p)))
;------------------------------------------------------------------------------
(defrule MarkVariantOperand
 "Moves through a given instruction and marks all variant operands as such"
 (Stage Analysis $?)
 ;(object (is-a Hint) (Type WavefrontSchedule) (Point Allow) (Parent ?t))
 (object (is-a BasicBlock) (ID ?p) (Parent ?t))
 (object (is-a Instruction) (ID ?name) (Parent ?p) (Operands $? ?target $?))
 (object (is-a TaggedObject) (ID ?target) (Parent ?p))
 =>
 ;(printout t ?name " is variant because of " ?target crlf)
 ;(assert (Instruction ?name dependent on ?target))
 (assert (Operand ?target variant for Instruction ?name))
 (assert (Operand ?target variant for BasicBlock ?p)))
;------------------------------------------------------------------------------
(defrule UpdateBasicBlockList-Variant
 "Updates the variant operands list of the target BasicBlock with the
 target operand"
 (declare (salience -1))
 (Stage Analysis $?)
 ?fct <- (Operand ?t variant for BasicBlock ?p)
 ?bb <- (object (is-a BasicBlock) (ID ?p))
 =>
 (retract ?fct)
 (modify-instance ?bb (VariantOperands (send ?bb get-VariantOperands) ?t)))
;------------------------------------------------------------------------------
(defrule UpdateBasicBlockList-Invariant
 "Updates the invariant operands list of the target BasicBlock with the
 target operand"
 (declare (salience -1))
 (Stage Analysis $?)
 ?fct <- (Operand ?t invariant for BasicBlock ?p)
 ?bb <- (object (is-a BasicBlock) (ID ?p))
 =>
 (retract ?fct)
 (modify-instance ?bb (InvariantOperands (send ?bb get-InvariantOperands) ?t)))
;------------------------------------------------------------------------------
(defrule UpdateInstructionList-Variant
 "Updates the variant operands list of the target Instruction with the
 target operand"
 (declare (salience -1))
 (Stage Analysis $?)
 ?fct <- (Operand ?t variant for Instruction ?p)
 ?bb <- (object (is-a Instruction) (ID ?p))
 =>
 (retract ?fct)
 (modify-instance ?bb (VariantOperands (send ?bb get-VariantOperands) ?t)))
;------------------------------------------------------------------------------
(defrule UpdateInstructionList-Invariant
 "Updates the invariant operands list of the target Instruction with the
 target operand"
 (declare (salience -1))
 (Stage Analysis $?)
 ?fct <- (Operand ?t invariant for Instruction ?p)
 ?bb <- (object (is-a Instruction) (ID ?p))
 =>
 (retract ?fct)
 (modify-instance ?bb (InvariantOperands (send ?bb get-InvariantOperands) ?t)))
;------------------------------------------------------------------------------
(defrule PrintInstructions
 (Stage Donuts $?)
 ?inst <- (object (is-a Instruction) 
  (Class ?c) (TimeIndex ?ti)
  (ID ?i) (Parent ?p))
 =>
 (bind ?ops (send ?inst get-Operands))
(printout t ?c " named " ?i " is part of block " ?p " at " ?ti crlf)
(foreach ?q ?ops
 (bind ?tmp (symbol-to-instance-name ?q))
 (if (instance-existp ?tmp) then
  (bind ?cl (class ?tmp))
 (printout t "  Operand " ?q " is of type " ?cl crlf)
 (if (or (eq ?cl ConstantExpression)
      (eq ?cl GlobalVariable)) then
  (bind ?tmp0 (send ?tmp get-Operands))
  (printout t "   Operands: " ?tmp0 crlf)
  (foreach ?qq ?tmp0
   (bind ?tmp1 (symbol-to-instance-name ?qq))
   (if (instance-existp ?tmp1) then
   (printout t "    Operand " ?qq " is a " (class ?tmp1) crlf)))
  else
 )
 else
 (printout t "  Operand " ?q " is a symbol" crlf)))
)
;------------------------------------------------------------------------------
