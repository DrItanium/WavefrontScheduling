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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defclass DependencyChain (is-a TaggedObject)
 (slot Producers (default-dynamic (make-instance (gensym*) of List)))
 (slot Consumers (default-dynamic (make-instance (gensym*) of List))))

(defmessage-handler DependencyChain init after ()
 (bind ?id (send ?self get-ID))
 (send ?self:Producers put-Parent ?id) 
 (send ?self:Consumers put-Parent ?id))
(defmessage-handler DependencyChain .ProducerCount ()
 (send ?self:Producers .Count))
(defmessage-handler DependencyChain .ConsumerCount ()
 (send ?self:Consumers .Count))
(defmessage-handler DependencyChain .AddProducers ($?p)
 (send ?self:Producers .AddRange ?p))
(defmessage-handler DependencyChain .AddProducer (?p) 
 "Adds a producer to the list of producers"
 (send ?self:Producers .SetAdd ?p))
(defmessage-handler DependencyChain .AddConsumer (?p)
 "Adds a producer to the list of consumers"
 (send ?self:Consumers .SetAdd ?p))

(defmessage-handler DependencyChain .AddConsumers ($?s)
 (send ?self:Consumers .AddRange ?s))

(defmessage-handler DependencyChain .IsProducer (?p)
 (send ?self:Producers .Contains ?p))

(defmessage-handler DependencyChain .IsConsumer (?p)
 (send ?self:Consumers .Contains ?p))

(defmessage-handler DependencyChain .HasProducers ()
 (not (send ?self:Producers .IsEmpty)))

(defmessage-handler DependencyChain .HasConsumers ()
 (not (send ?self:Consumers .IsEmpty)))

(defmessage-handler DependencyChain .RemoveConsumer (?v)
  (send ?self:Consumers .Remove ?v))

(defmessage-handler DependencyChain .RemoveProducer (?v)
  (send ?self:Producers .Remove ?v))

(defmessage-handler DependencyChain .ProducersContainsSubset ($?v)
 (send ?self:Producers .ContainsSubset $?v))

(defmessage-handler DependencyChain .ConsumersContainsSubset ($?v)
 (send ?self:Consumers .ContainsSubset $?v))

(defmessage-handler DependencyChain .Producers () 
 "Returns the list of producers from the dependency information"
 (return (send ?self:Producers get-Contents)))

(defmessage-handler DependencyChain .Consumers () 
 "Returns the list of consumers from the dependency information"
 (return (send ?self:Consumers get-Contents)))


