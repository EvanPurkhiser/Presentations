// Get the presentation to display
var mdUri = 'presentations/' + window.location.search.substring(1) + '.md';

// Set the uri to the presentation markdown file
window.document.getElementById('md').setAttribute('data-markdown', mdUri);

Reveal.initialize({

	progress: false,

	transition: 'default',           // default/cube/page/concave/zoom/linear/fade/none
	transitionSpeed: 'default',      // default/fast/slow
	backgroundTransition: 'default', // default/linear/none
});
