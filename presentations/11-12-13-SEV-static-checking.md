## Invariant Inference for Static Checking: An Emperical Evaluation

Jeremy W. Nimmer & Michael D. Ernst

Presentation by Evan Purkhiser


### [Michael D. Ernst](http://homes.cs.washington.edu/~mernst/)

 * Associate Professor at University of Washington
 * Primary research interest in programmer productivity
 * Previously a research at Microsoft Research
 * Has [_many_ publications](http://homes.cs.washington.edu/~mernst/pubs/)


![Michael Ernst](http://homes.cs.washington.edu/~mernst/images/mernst-headshot.jpg)


### Jeremy W. Nimmer

![Who is he?!?](http://buildingmarkets.org/blogs/wp-content/blogs.dir/1/files/2010/04/mystman.jpg)

I'm not entirely convinced this person actually exists.


# Background


## Static Analysis

 * Technique for detecting and checking properties of programs
 * Formatting errors, pointer errors, memory leaks
 * Useful because it allows us to find problems sooner
 * Sometimes also called 'Linting' (more popular today)
 * Already widely used


### Lightweight theorem proving

 * Use annotations to set 'goals'
 * Offers more fine grained checking over static analysis
 * Often not used in practice due to difficulty of use
 * Known as "[Extended Static Checking](http://en.wikipedia.org/wiki/Extended_static_checkin)"
