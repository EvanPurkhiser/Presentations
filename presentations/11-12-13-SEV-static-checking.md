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


## Selected Programs

 ![Selected Programs](selected-programs.svg)


## Participants

 * 47 Students participated
 * Really only 41 as 6 were disqualified
 * Volunteers
 * Mostly graduate students from MIT or University of Washington


 ![Participants](participants.svg)


## Experiment Design

 * All users started with 3-6 annotations already inserted
 * 5 different 'treatments'
   * Control
   * Houdini
   * Daikon {tiny,small,good}


### Control

This group did not have any tool assistance. They must add all the annotations on their own.


### Houdini

 * Provided the Houdini tool (invoked when running `escjava`)
 * Needed to add enough annotations so Houdini could fully annotate the program


### Daikon

 * Daikon had already been run prior to receiving the program
 * Not provided with the test suit
 * Three different Daikon treatments


### Diakon: Tiny

 * Very few test cases
 * Very little edge case coverage
 * Meant to simulate projects with a poor test suite


### Diakon: Small

Slightly better tests than in the tiny treatment


### Diakon: Good

Ran with a test suite that provided 100% (or close) code coverage


![Diakon Sets](diakon-sets.svg)


## Measurements

 * Primarily interested on the effect of the annotation tools
 * Success and time spent are easy to measure
 * Measuring annotations is a little harder...


![Measurements](measurements.svg)


### Measurement Techniques

 * Success: Did they finish within time?
 * To determine 'nearest correct' answer the authors manually edited the
   annotations until they became correct.
 * Some automatic grading was done to determine correct sets - May fail with
   essoteric annotations though


### Computed values

 * **Precision** - Correctness of annotations: $\frac{correct}{written}$
 * **Recall** - The number of nessicary annotations: $\frac{correct}{verifiable}$
 * **Bonus** - Additional annotations expressed: $\frac{verifiable}{minimal}$
 * **Unnecessiary** - Extra effort that Houdini could have handled
 * **Boost** - How much Houdini contributed


![Visualization](visualization.svg)
