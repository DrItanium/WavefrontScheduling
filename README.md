This is one half of my masters thesis. The objective of which was to apply
wavefront scheduling to superscalar processors. The other aspect required is
LibExpertSystem. I have kept them separate because they are technically
standalone.

However, this code will NOT work in a standard clips build. There are functions
defined in LibExpertSystem that this implementation requires. 

Whoever you are, I hope you enjoy perusing through this code. It was a lot of
fun to write. 

The only requirement I have is that you MUST use clips 630 beta or higher. I
use the foreach statement in several parts (11th hour change....) which was
introduced in 630.

At this point, using the expert system is a very manual process. You have to
place the ExpertSystem.so (on linux) in the same folder as the CLIPS source
code. I have been looking into preloading structures but CLIPS has not been
playing nice. So at this point you need to run this optimization with opt. 
There is no integration with clang or anything like that.

-Joshua Scoggins
