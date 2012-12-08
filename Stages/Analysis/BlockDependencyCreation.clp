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
; BlockDependencyCreation.clp - Contains rules pertaining to the creation of
; data dependencies between different instructions inside of a basic block
; Written by Joshua Scoggins (7/1/2012)
;------------------------------------------------------------------------------
(defrule MarkLocalDependency-Call
 			(declare (salience 1))
         (Stage Analysis $?)
         (object (is-a CallInstruction) (Parent ?p) (ID ?t0) 
                        (ArgumentOperands $? ?o $?))
         (object (is-a Instruction) (ID ?o) (Parent ?p))
         =>
			(assert ({ env: clips 
			           action: dependency-announce
				        type: produces
				        target: ?o
				        other: ?t0 })
			        ({ env: clips
			           action: dependency-announce
			       	  type: consumes
			       	  target: ?t0
			       	  other: ?o })))
;------------------------------------------------------------------------------
(defrule MarkLocalDependency 
         (Stage Analysis $?)
         ?i0 <- (object (is-a Instruction&~CallInstruction) (Parent ?p) (ID ?t0) 
                        (Operands $? ?o $?))
         (object (is-a Instruction) (ID ?o) (Parent ?p))
         =>
			(assert ({ env: clips 
			           action: dependency-announce
				        type: produces
				        target: ?o
				        other: ?t0 })
			        ({ env: clips
			           action: dependency-announce
			       	  type: consumes
			       	  target: ?t0
			       	  other: ?o })))
;------------------------------------------------------------------------------
(defrule MarkInstructionsThatHappenBeforeCall-WritesToMemory
         (Stage Analysis $?)
         (object (is-a BasicBlock) (ID ?v) (Contents $?before ?n0 $?))
         (object (is-a CallInstruction) (ID ?n0) (Parent ?v) 
                 (MayWriteToMemory TRUE))
         =>
         (progn$ (?n1 ?before)
			(assert ({ env: clips 
			           action: dependency-announce
				        type: produces
				        target: ?n1
				        other: ?n0 })
			        ({ env: clips
			           action: dependency-announce
			       	  type: consumes
			       	  target: ?n0
			       	  other: ?n1 }))))
;------------------------------------------------------------------------------
(defrule MarkInstructionsThatHappenBeforeCall-HasSideEffects
         (Stage Analysis $?)
         (object (is-a BasicBlock) (ID ?p) (Contents $?a ?n0 $?))
         (object (is-a CallInstruction) (ID ?n0) (Parent ?p)
                 (MayHaveSideEffects TRUE))
         =>
         (progn$ (?n1 ?a)
			(assert ({ env: clips 
			           action: dependency-announce
				        type: produces
				        target: ?n1
				        other: ?n0 })
			        ({ env: clips
			           action: dependency-announce
			       	  type: consumes
			       	  target: ?n0
			       	  other: ?n1 }))))
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-ModifiesMemory
         "Creates a series of dependencies for all instructions following a 
         call instruction if it turns out that the call could modify memory."
         (Stage Analysis $?)
         (object (is-a BasicBlock) (ID ?p) (Contents $? ?name $?rest))
         (object (is-a CallInstruction) (ID ?name) (Parent ?p)
                 (MayWriteToMemory TRUE))
         =>
			(assert ({ env: clips
						  action: call-barrier
						  type: element
						  target: ?p }))
         (progn$ (?following ?rest)
			(assert ({ env: clips 
			           action: dependency-announce
				        type: produces
				        target: ?name
				        other: ?following })
			       ; ({ env: clips
			       ;    action: dependency-announce
			       ;	  type: consumes
			       ;	  target: ?following
			       ;	  other: ?name })
			        ({ env: clips
						  action: call-dependency
						  type: instruction
						  target: ?following }))))
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-InlineAsm
         "Creates a series of dependencies for all instructions following a 
         call instruction if it turns out that the call is inline asm."
         (Stage Analysis $?)
         (object (is-a BasicBlock) (ID ?p) (Contents $? ?name $?rest))
         (object (is-a CallInstruction) (ID ?name) (Parent ?p) 
                 (IsInlineAsm TRUE))
         =>
			(assert ({ env: clips
						  action: call-barrier
						  type: element
						  target: ?p }))
         (progn$ (?following ?rest)
			(assert ({ env: clips 
			           action: dependency-announce
				        type: produces
				        target: ?name
				        other: ?following })
			       ; ({ env: clips
			       ;    action: dependency-announce
			       ;	  type: consumes
			       ;	  target: ?following
			       ;	  other: ?name })
			        ({ env: clips
						  action: call-dependency
						  type: instruction
						  target: ?following }))))
;------------------------------------------------------------------------------
(defrule MarkCallInstructionDependency-SideEffects
         "Creates a series of dependencies for all instructions following a 
         call instruction if it turns out that the call has side effects."
         (Stage Analysis $?)
         (object (is-a CallInstruction) (ID ?name) (Parent ?p)
                 (MayHaveSideEffects TRUE)) 
         (object (is-a BasicBlock) (ID ?p) (Contents $? ?name $?rest))
         =>
			(assert ({ env: clips
						  action: call-barrier
						  type: element
						  target: ?p }))
         (progn$ (?following ?rest)
			(assert ({ env: clips 
			           action: dependency-announce
				        type: produces
				        target: ?name
				        other: ?following })
			       ; ({ env: clips
			       ;    action: dependency-announce
			       ;	  type: consumes
			       ;	  target: ?following
			       ;	  other: ?name })
			        ({ env: clips
						  action: call-dependency
						  type: instruction
						  target: ?following }))))
;------------------------------------------------------------------------------
(defrule FlagCallBarrierForDiplomat-HasParent
         ;(declare (salience -10))
         (Stage Analysis-Update $?)
			?fct <- ({ env: clips 
				        action: call-barrier
						  type: element
						  target: ?z })
         ?d <- (object (is-a Diplomat) (ID ?z) (Parent ?p) 
                       (HasCallBarrier FALSE))
         (exists (object (is-a Diplomat) (ID ?p)))
         =>
         (retract ?fct)
			(assert ({ env: clips
						  action: call-barrier
						  type: element
						  target: ?p }))
         (modify-instance ?d (HasCallBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule PropagateCallBarrierForDiplomat-HasParent
         ;(declare (salience -10))
         (Stage Analysis-Update $?)
			?fct <- ({ env: clips 
				        action: call-barrier
						  type: element
						  target: ?z })
         ?d <- (object (is-a Diplomat) (ID ?z) (Parent ?p) 
                       (HasCallBarrier TRUE))
         (exists (object (is-a Diplomat) (ID ?p)))
         =>
         (retract ?fct)
			(assert ({ env: clips
						  action: call-barrier
						  type: element
						  target: ?p })))
;------------------------------------------------------------------------------
(defrule FlagCallBarrierForDiplomat-NoParent
         ;(declare (salience -10))
         (Stage Analysis-Update $?)
			?fct <- ({ env: clips 
				        action: call-barrier
						  type: element
						  target: ?z })
         ?d <- (object (is-a Diplomat) (ID ?z) (Parent ?p) 
                       (HasCallBarrier FALSE))
         (not (exists (object (is-a Diplomat) (ID ?p))))
         =>
         (retract ?fct)
         (modify-instance ?d (HasCallBarrier TRUE)))
;------------------------------------------------------------------------------
(defrule PropagateCallBarrierForDiplomat-NoParent
         ;(declare (salience -10))
         (Stage Analysis-Update $?)
			?fct <- ({ env: clips 
				        action: call-barrier
						  type: element
						  target: ?z })
         ?d <- (object (is-a Diplomat) (ID ?z) (Parent ?p) 
                       (HasCallBarrier TRUE))
         (not (exists (object (is-a Diplomat) (ID ?p))))
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule MarkHasACallDependency-Set
         (Stage Analysis-Update $?)
			?fct <- ({ env: clips
						  action: call-dependency
						  type: instruction
						  target: ?target })
         ?inst <- (object (is-a Instruction) (ID ?target) 
                          (HasCallDependency FALSE))
         =>
         (retract ?fct)
         (modify-instance ?inst (HasCallDependency TRUE)))
;------------------------------------------------------------------------------
(defrule MarkHasACallDependency-Ignore
         (Stage Analysis-Update $?)
			?fct <- ({ env: clips
						  action: call-dependency
						  type: instruction
						  target: ?target })
         ?inst <- (object (is-a Instruction) (ID ?target) 
                          (HasCallDependency TRUE))
         =>
         (retract ?fct))
;------------------------------------------------------------------------------
(defrule StoreToLoadDependency
         (Stage ExtendedMemoryAnalysis $?)
         (object (is-a StoreInstruction) (Parent ?p) (ID ?t0)
                 (TimeIndex ?ti0) (MemoryTarget ?sym0))
         (object (is-a LoadInstruction) (Parent ?p) (ID ?t1) 
                 (TimeIndex ?ti1&:(< ?ti0 ?ti1)) (MemoryTarget ?sym1))
         (test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
         =>
			(assert ({ env: clips 
			           action: dependency-announce
				        type: produces
				        target: ?t0
				        other: ?t1 })
			        ({ env: clips
			           action: dependency-announce
			       	  type: consumes
			       	  target: ?t1
			       	  other: ?t0 })))
;------------------------------------------------------------------------------
(defrule StoreToStoreDependency
         (Stage ExtendedMemoryAnalysis $?)
         (object (is-a StoreInstruction) (Parent ?p) (ID ?t0)
                 (TimeIndex ?ti0) (MemoryTarget ?sym0))
         (object (is-a StoreInstruction) (Parent ?p) (ID ?t1) 
                 (TimeIndex ?ti1&:(< ?ti0 ?ti1)) (MemoryTarget ?sym1))
         (test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
         =>
			(assert ({ env: clips 
			           action: dependency-announce
				        type: produces
				        target: ?t0
				        other: ?t1 })
			        ({ env: clips
			           action: dependency-announce
			       	  type: consumes
			       	  target: ?t1
			       	  other: ?t0 })))
;------------------------------------------------------------------------------
(defrule LoadToStoreDependency
         (Stage ExtendedMemoryAnalysis $?)
         (object (is-a LoadInstruction) (Parent ?p) (ID ?t0)
                 (TimeIndex ?ti0) (MemoryTarget ?sym0)) 
         (object (is-a StoreInstruction) (Parent ?p) (ID ?t1) 
                 (TimeIndex ?ti1&:(< ?ti0 ?ti1)) (MemoryTarget ?sym1))
         (test (or (eq ?sym0 ?sym1) (eq ?sym0 UNKNOWN)))
         =>
			(assert ({ env: clips 
			           action: dependency-announce
				        type: produces
				        target: ?t0
				        other: ?t1 })
			        ({ env: clips
			           action: dependency-announce
			       	  type: consumes
			       	  target: ?t1
			       	  other: ?t0 })))
;------------------------------------------------------------------------------
