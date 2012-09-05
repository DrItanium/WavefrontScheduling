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
(defclass Diplomat 
 "A Diplomat is a collection of fields that interact with other
 objects."
 (is-a LLVMObject)
 (slot IsOpen (type SYMBOL) (visibility public) 
	(allowed-values FALSE TRUE))
 (slot HasCallBarrier (type SYMBOL) (visibility public) 
  (allowed-values FALSE TRUE))
 (slot HasMemoryBarrier (type SYMBOL) (visibility public) 
  (allowed-values FALSE TRUE))
 (multislot PreviousPathElements (visibility public))
 (multislot NextPathElements (visibility public))
 (multislot Consumes)
 (multislot Produces)
 ;(multislot Chokes (visibility public))
 ;(multislot ChokedBy (visibility public))
 (multislot Paths (visibility public)))
 ;(multislot RegionalAllies (visibility public))
 ;(multislot FunctionalAllies (visibility public)))

;(defmessage-handler Diplomat .AddRegionalAlly (?a)
; (bind ?self:RegionalAllies (create$ ?self:RegionalAllies ?a)))
;
;(defmessage-handler Diplomat .AddFunctionalAlly (?a)
; (bind ?self:FunctionalAllies (create$ ?self:FunctionalAllies ?a)))

;(defmessage-handler Diplomat .AddPath (?path)
; (bind ?self:Paths (create$ ?self:Paths ?path)))

;(defmessage-handler Diplomat .AddChokes (?blk)
; (bind ?self:Chokes (create$ ?self:Chokes ?blk)))
;
;(defmessage-handler Diplomat .AddChokedBy (?blk)
; (bind ?self:ChokedBy (create$ ?self:ChokedBy ?blk)))

