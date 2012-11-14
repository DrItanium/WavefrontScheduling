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
; Hint.clp - Contains the basic hint type plus a few ease of access sub types
;            Hints are my way of quickly creating objects that map a single
;            object to a series of other objects. A hint also contains a type
;            field that allows hints to be further constrained by another type.
;            Suprisingly enough hints are quite useful as they allow facts to
;            be created with a minimal amount of effort yet are very expressive
;            in their contents. 
;
;            They can also keep track of the number of references they have
; Written by Joshua Scoggins
;------------------------------------------------------------------------------
(defclass Hint (is-a List)
  (slot Type (visibility public) (default nil))
  (slot Point (default nil))
  (slot ReferenceCount (visibility public) (type NUMBER)))

;------------------------------------------------------------------------------
(defmessage-handler Hint .IncrementReferenceCount ()
						  (bind ?self:ReferenceCount (+ ?self:ReferenceCount 1)))
;------------------------------------------------------------------------------
(defmessage-handler Hint .DecrementReferenceCount ()
						  (bind ?self:ReferenceCount (- ?self:ReferenceCount 1)))
;------------------------------------------------------------------------------
(deffunction hints-of-type-with-point (?type ?point)
				 "Gets all hints with the specified type and point"
				 (find-all-instances ((?h Hint)) 
											(and (eq ?type (send ?h get-Type))
												  (eq ?point (send ?h get-Point)))))
;------------------------------------------------------------------------------
(deffunction hints-of-type (?type)
				 "Returns all hints of a given type"
				 (find-all-instances ((?h Hint)) (eq ?type (send ?h get-Type))))
;------------------------------------------------------------------------------
(deffunction hintp (?instance)
				 (if (or (instance-namep ?instance) 
							(instance-addressp ?instance)) then
					(bind ?conv ?instance)
					else
					(bind ?conv (symbol-to-instance-name ?instance)))
				 (return (eq (class ?conv) Hint)))
;------------------------------------------------------------------------------
(defclass Path (is-a Hint)
  (slot ExitBlock (type SYMBOL))
  (slot Closed (type SYMBOL) (allowed-values FALSE TRUE)))
;------------------------------------------------------------------------------
(defmessage-handler Path init after ()
						  (bind ?self:Type Path))
;------------------------------------------------------------------------------
(defclass Hierarchy (is-a Hint))
;------------------------------------------------------------------------------
(defmessage-handler Hierarchy init after ()
						  (bind ?self:Type Hierarchy))
;------------------------------------------------------------------------------
(defclass FrequencyAnalysis (is-a Hint)
  (slot Frequency (type NUMBER) (range 0 ?VARIABLE)))
;------------------------------------------------------------------------------
(defmessage-handler FrequencyAnalysis init after ()
						  (bind ?self:Type FrequencyAnalysis))
;------------------------------------------------------------------------------
(defmessage-handler FrequencyAnalysis .IncrementFrequency ()
						  (bind ?self:Frequency (+ 1 ?self:Frequency)))
;------------------------------------------------------------------------------
(defclass FlatList (is-a Hint))
;------------------------------------------------------------------------------
(defmessage-handler FlatList init after ()
						  (bind ?self:Type FlatList))
;------------------------------------------------------------------------------
