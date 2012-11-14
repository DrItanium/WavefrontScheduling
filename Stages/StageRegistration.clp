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
; Defines the series that the expert system will execute through on invocation
; It works through a fact definition structure
;------------------------------------------------------------------------------
(defrule first-rule-has-loops
			(declare (salience 10000))
			(initial-fact)
			(exists (object (is-a Loop)))
			=>
			(assert (Stage BuildFlatList
								ExpandFlatList
								ClaimOwnership
								Arbitrate
								ResolveClaims
								DeterminantConstruction
								DeterminantPopulation
								DeterminantResolution
								DeterminantIndirectResolution
								Fixup 
								FixupUpdate
								FixupRename
								CleanUp-Merger
								ModificationPropagation
								Analysis 
								ExtendedMemoryAnalysis
								Path
								PathUpdate
								WavefrontInit
								WavefrontSchedule
								WavefrontFinal
								Final)))
;------------------------------------------------------------------------------
(defrule first-rule-no-loops 
			(declare (salience 10000))
			(initial-fact)
			(not (exists (object (is-a Loop))))
			=>
			(assert (Stage ModificationPropagation
								Analysis 
								ExtendedMemoryAnalysis
								Path
								PathUpdate
								WavefrontInit
								WavefrontSchedule
								WavefrontFinal
								Final)))
;------------------------------------------------------------------------------
(defrule change-stage
			(declare (salience -10000))
			?fct <- (Stage ? $?rest)
			=>
			(retract ?fct)
			(assert (Stage $?rest)))
;------------------------------------------------------------------------------
