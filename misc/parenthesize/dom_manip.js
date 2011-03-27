// requires 'parenthesize.js' being included before

function $(id)
{
  return document.getElementById(id);
}

// cleans output area
function cleanOutputArea()
{
  // just removes all the children of the 'output' div
  var outputArea = $('output');
  while (outputArea.hasChildNodes()) {
    outputArea.removeChild(outputArea.firstChild);
  }
}

// adds a solution to the output area
function addSolution(sol)
{
  // creates a paragraph node for the solution
  var solutionP = document.createElement('p');
  var solutionTxt = document.createTextNode(sol);
  solutionP.appendChild(solutionTxt);
  solutionP.className = 'sol';
  
  // appends this node to the output area
  $('output').appendChild(solutionP);
}

// adds an error message to the output area
function addError(error)
{
  // creates a paragraph node for the error
  var errorP = document.createElement('p');
  var errorTxt = document.createTextNode(error);
  errorP.appendChild(errorTxt);
  errorP.className = 'error';
  
  // appends this node to the output area
  $('output').appendChild(errorP);
}

// updates parenthesizations
function updateParenthesizations(expr, result)
{
  // cleans up output area
  cleanOutputArea();
  
  // if one or more of the inputs are empty, exits without error
  if (expr === '' || result === '') {
    return;
  }
  
  // checks these strings
  var error = false;
  if (!EXPRESSION_RE.test(expr)) {
    addError('Invalid expression syntax.');
    error = true;
  }
  if (!RESULT_RE.test(result)) {
    addError('Invalid result syntax.');
    error = true;
  }
  if (error) {
    return;
  }
  
  // gets the solutions
  try {
    var sols = parenthesize(expr, result);
  } catch(e) {
    alert('INTERNAL ERROR');
    return;
  }
  
  // if there are solutions, adds them to the output area
  if (sols.length > 0) {
    for (var i = 0; i < sols.length; i++) {
      addSolution(sols[i]);
    }
  } else {
    addError('There are no solutions.');
  }
}
