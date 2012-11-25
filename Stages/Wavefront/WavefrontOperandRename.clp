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
; Now we need to rename operands as need be within the blocks that these
; instructions have been scheduled into
;------------------------------------------------------------------------------
(defrule AssertReplacementActions
			"Iterates through the replacement actions multifield and asserts facts 
			related to the replacement of given values with another value"
			(declare (salience 100))
			(Stage WavefrontSchedule $?)
			(Substage Rename $?)
			(object (is-a PathAggregate) (Parent ?e) 
					  (ReplacementActions $? ?orig ?new ! $?))
			=>
			; I have turned you into a cheese sandwich, what do you say to that?
			(assert (Replace uses of ?orig with ?new for block ?e)))
;------------------------------------------------------------------------------
(defrule ReplaceUses
			(declare (salience 20))
			(Stage WavefrontSchedule $?)
			(Substage Rename $?)
			?fct <- (Replace uses of ?orig with ?new for block ?e)
			(object (is-a Instruction) (ID ?orig) (Pointer ?oPtr))
			(object (is-a Instruction) (ID ?new) (Pointer ?nPtr))
			(object (is-a BasicBlock) (ID ?e) (Contents $? ?new $?rest))
			=>
			(retract ?fct)
			(bind ?ptrList (create$))
			(bind ?symList (create$))
      (bind ?i0 1)
			(progn$ (?var $?rest)
					  (bind ?obj (symbol-to-instance-name ?var))
            (if (member$ ?orig (send ?obj get-Operands)) then
             (bind ?ptrList (insert$ ?ptrList ?i0 (send ?obj get-Pointer)))
             (bind ?symList (insert$ ?symList ?i0 ?var))
            (bind ?i0 (+ ?i0 1))))
      (assert ({ clips ! ?orig => ?new for ?symList })
              ({ llvm ! ?oPtr => ?nPtr for ?ptrList })))
;------------------------------------------------------------------------------
(defrule ReplaceUsesInLLVM
			(declare (salience -1))
			(Stage WavefrontSchedule $?)
			(Substage Rename $?)
      ?fct <- ({ llvm ! ?from => ?to for $?p2 })
			=>
			(if (llvm-replace-uses ?from ?to ?p2) then 
			  (retract ?fct) 
			  else
			  (printout t
							"Some kind of error occured when trying to replace uses. " 
							crlf "Make sure that you've done arguments correctly. " 
							crlf "The failing rule is ReplaceUsesInLLVM." crlf
							"?from = " ?from crlf
							"?to = " ?to crlf
							"?p2 = " ?p2 crlf
							"Now I'm exiting" crlf)
			  (exit)))
;------------------------------------------------------------------------------
(defrule ReplaceUsesInCLIPS
			(declare (salience -1))
			(Stage WavefrontSchedule $?)
			(Substage Rename $?)
      ?fct <- ({ clips ! ?from => ?to for ?symbol $?rest })
			?inst <- (object (is-a Instruction) (ID ?symbol) 
								  (Operands $?operands) (LocalDependencies $?locDep)
								  (NonLocalDependencies $?nLocDep))
			=>
			(modify-instance ?inst (Operands) (LocalDependencies) 
			 (NonLocalDependencies))
			(retract ?fct)
      (assert ({ clips ! ?from => ?to for $?rest })
              ({ clips ! ?from => ?to replacement ?symbol 
               operands $?operands })
				  ({ env: clips translation: ?from => ?to action: replacement
					  in: ?symbol type: local-dependencies
					  contents: $?locDep })
				  ({ env: clips translation: ?from => ?to action: replacement
						in: ?symbol type: non-local-dependencies
						contents: $?nLocDep })))
;------------------------------------------------------------------------------
(defrule ReplaceUsesInCLIPS-End
			(declare (salience -1))
			(Stage WavefrontSchedule $?)
			(Substage Rename $?)
      ?fct <- ({ clips ! ?from => ?to for })
			=>
			(retract ?fct))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualLocalDependencyEntries-NoMatch
 (declare (salience -2))
  (Stage WavefrontSchedule $?)
  (Substage Rename $?)
  ?fct <- ({
	  	env: clips
		translation: ?from => ?to 
		action: replacement
		in: ?symbol 
		type: local-dependencies
		contents: ?curr&~?from $?rest
	  })
  ?inst <- (object (is-a Instruction) (ID ?symbol))
  =>
  (object-pattern-match-delay
  (slot-insert$ ?inst LocalDependencies 1 ?curr)
  (retract ?fct)
  (assert ({ env: clips translation: ?from => ?to action: replacement in:
			  ?symbol type: local-dependencies contents: $?rest }))))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualLocalDependencyEntries-Match
 (declare (salience -2))
  (Stage WavefrontSchedule $?)
  (Substage Rename $?)
  ?fct <- ({
	  	env: clips
		translation: ?from => ?to 
		action: replacement
		in: ?symbol 
		type: local-dependencies
		contents: ?from $?rest
	  })
  ?inst <- (object (is-a Instruction) (ID ?symbol))
  =>
  (object-pattern-match-delay
  (slot-insert$ ?inst LocalDependencies 1 ?to)
  (retract ?fct)
  (assert ({ env: clips translation: ?from => ?to action: replacement in:
			  ?symbol type: local-dependencies contents: $?rest }))))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualNonLocalDependencyEntries-NoMatch
 (declare (salience -2))
  (Stage WavefrontSchedule $?)
  (Substage Rename $?)
  ?fct <- ({
	  	env: clips
		translation: ?from => ?to 
		action: replacement
		in: ?symbol 
		type: non-local-dependencies
		contents: ?curr&~?from $?rest
	  })
  ?inst <- (object (is-a Instruction) (ID ?symbol))
  =>
  (object-pattern-match-delay
  (slot-insert$ ?inst NonLocalDependencies 1 ?curr)
  (retract ?fct)
  (assert ({ env: clips translation: ?from => ?to action: replacement in:
			  ?symbol type: local-dependencies contents: $?rest }))))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualNonLocalDependencyEntries-Match
 (declare (salience -2))
  (Stage WavefrontSchedule $?)
  (Substage Rename $?)
  ?fct <- ({
	  	env: clips
		translation: ?from => ?to 
		action: replacement
		in: ?symbol 
		type: non-local-dependencies
		contents: ?from $?rest
	  })
  ?inst <- (object (is-a Instruction) (ID ?symbol))
  =>
  (object-pattern-match-delay
  (slot-insert$ ?inst NonLocalDependencies 1 ?to)
  (retract ?fct)
  (assert ({ env: clips translation: ?from => ?to action: replacement in:
			  ?symbol type: non-local-dependencies contents: $?rest }))))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualInstructionUses-NoMatch
			(declare (salience -2))
			(Stage WavefrontSchedule $?)
			(Substage Rename $?)
      ?fct <- ({ clips ! ?f => ?t replacement ?s operands ?op&~?f $?ops })
			?inst <- (object (is-a Instruction) (ID ?s))
			=>
			(slot-insert$ ?inst Operands 1 ?op)
			(retract ?fct)
      (assert ({ clips ! ?f => ?t replacement ?s operands $?ops })))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualInstructionUses-Match
			(declare (salience -2))
			(Stage WavefrontSchedule $?)
			(Substage Rename $?)
      ?fct <- ({ clips ! ?f => ?t replacement ?s operands ?f $?ops })
			?inst <- (object (is-a Instruction) (ID ?s))
			=>
			(slot-insert$ ?inst Operands 1 ?t)
			(retract ?fct)
      (assert ({ clips ! ?f => ?t replacement ?s operands $?ops })))
;------------------------------------------------------------------------------
(defrule ReplaceIndividualInstructionUses-Empty
			(declare (salience -2))
			(Stage WavefrontSchedule $?)
			(Substage Rename $?)
      ?fct <- ({ clips ! ?f => ?t replacement ?s operands })
			=>
			(retract ?fct))
;------------------------------------------------------------------------------
