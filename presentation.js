// Get the presentation to display
var path  = 'presentations/' + window.location.search.substring(1);
var mdUri = path + '.md';

// Set the uri to the presentation markdown file
document.getElementById('md').setAttribute('data-markdown', mdUri);

// Setup reveal.js
Reveal.initialize({

	progress: false,

	transition: 'linear',            // default/cube/page/concave/zoom/linear/fade/none
	transitionSpeed: 'default',      // default/fast/slow
	backgroundTransition: 'default', // default/linear/none

	dependencies: [
		{ src: "http://cdn.jsdelivr.net/reveal.js/2.5.0/plugin/markdown/marked.js" },
		{ src: "http://cdn.jsdelivr.net/reveal.js/2.5.0/plugin/markdown/markdown.js" },

		{
			src: "http://cdn.jsdelivr.net/reveal.js/2.5.0/plugin/highlight/highlight.js",
			async: true,
			callback: function() { hljs.initHighlightingOnLoad(); }
		},
	],
});

// Add page numbers
// https://github.com/hakimel/reveal.js/pull/56#issuecomment-20245613
function slidenumber(event){
	var totalslides = document.querySelectorAll( '.reveal .slides section:not(.stack)' ).length;
	var current_slide = 0;

	var horizontal_slides = document.querySelectorAll( '.reveal .slides>section' );
	for (var i = 0; i < event.indexh; i++) {
		// get subslides
		var subslides = horizontal_slides[i].querySelectorAll('section');

		// if subslides.length is 0, add 1 for horizontal slide, else add subslides.length
		current_slide += (subslides.length === 0) ? 1 : subslides.length;
	}

	current_slide += event.indexv+1;
	return current_slide.toString()+"/"+totalslides.toString();
}

Reveal.addEventListener('slidechanged', function(event){
	document.querySelector('.slidenumber').innerText=slidenumber(event);
});
Reveal.addEventListener('ready', function(event){
	document.querySelector('.slidenumber').innerText=slidenumber(event);

	Array.prototype.forEach.call(document.querySelectorAll('.reveal section  img'), function(element)
	{
		var src = element.getAttribute('src');

		if (src.indexOf('//') == -1)
		{
			element.src = path + '/' + src
		}
	});
});
