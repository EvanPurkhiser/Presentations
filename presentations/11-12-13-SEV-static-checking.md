## Invariant Inference for Static Checking: Empirical Evaluation

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


## ESC/Java

 * A Java Extended Static Checker tool
 * Annotations must be written similar to `assert` statements
 * Issues warnings about annotations that can't be verified
 * Also includes suggestions for correcting the problem


Example with annotations

```java
public class StackAr {
	//@ invariant theArray != null
	//@ invariant \typeof(theArray) == \type(Object[])
	//@ invariant topOfStack >= -1
	//@ invariant topOfStack <= theArray.length-1
	/*@ invariant (\forall int i; (0 <= i &&
		i <= topOfStack) ==> (theArray[i] != null)) */
	/*@ invariant (\forall int i; (topOfStack+1 <= i &&
		i <= theArray.length-1) ==> (theArray[i] == null)) */

	private Object [ ] theArray;
	private int topOfStack;

	//@ requires capacity >= 0
	//@ ensures capacity == theArray.length
	//@ ensures topOfStack == -1
	public StackAr( int capacity ) {
		theArray = new Object[ capacity ];
		topOfStack = -1;
	}
}
```


Continued...

```java
public class StackAr {
	//@ modifies topOfStack, theArray[*]
	//@ ensures (\result != null) == (\old(topOfStack) >= 0)
	//@ ensures topOfStack <= \old(topOfStack)
	/*@ ensures (\old(topOfStack) >= 0) ==>
		(topOfStack == \old(topOfStack) - 1) */
	/*@ ensures (\forall int i; (0 <= i && i <= topOfStack)
		==> (theArray[i] == \old(theArray[i]))) */
	public Object topAndPop( ) {
		if( isEmpty( ) )
			return null;
		Object topItem = top( );
		theArray[ topOfStack-- ] = null;
		return topItem;
	}
}
```


### Invariants?

A condition that can be relied upon to be true during execution of a program, or
during some portion of it.


But no one wants to write all those an annotations...


## Houdini

 * An 'annotation assistant' tool
 * Generates candidate annotation sets
 * Checks each annotation set with ESC/Java, discarding unprovable annotations
   until all are provable
 * Exhaustive filtering


### But really.. "Whodini"

 * Houdini was unavailable to the researchers
 * "Whodini" is a re-implementation based on documentation
 * Supposedly runs faster than Houdini
 * But still takes 10-60 seconds on the given programs..


## Daikon

 * Detects program invariants dynamically during execution
 * Examines computed values and detects patterns
 * Invariants determined by checking at each entry / exit point
 * Dependant on the quality and completeness of the tests
 * Does _not_ verify the generated invariants
 * Various language and output format support


# Methodology


## Given Task

 * Participants given a class to Anotate
 * Allocated a single hour to complete the task
 * Goal is to annotate the program until ESC/Java gives no warnings / errors (Therefore no runtime exceptions)
