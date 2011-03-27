EXPRESSION_RE = /^\s*(\d+(\.\d+)?\s*(\+|-|\*|\/)\s*)*\d+(\.\d+)?\s*$/;
RESULT_RE = /^\s*\d+(\.\d+)?\s*$/;

// updates the permutation to the next, in lexicographic order
// returns false if already at the last one
function updPerm(a)
{
  // http://en.wikipedia.org/wiki/Permutation#Systematic_generation_of_all_permutations

  // - Find the largest index k such that a[k] < a[k + 1]. If no such index exists, the permutation is the last permutation.
  // - Find the largest index l such that a[k] < a[l]. Since k + 1 is such an index, l is well defined and satisfies k < l.
  // - Swap a[k] with a[l].
  // - Reverse the sequence from a[k + 1] up to and including the final element a[n].
  for (k = a.length - 2; k >= 0; k--) {
    if (a[k] < a[k+1]) {
      break;
    }
  }
  if (k < 0) {
    return false;
  }
  var l;
  for (l = a.length - 1; l >= 0; l--) {
    if (a[k] < a[l]) {
      break;
    }
  }
  var tmp = a[k];
  a[k] = a[l];
  a[l] = tmp;
  for (var x1 = k + 1, x2 = a.length - 1; x1 < x2; x1++, x2--) {
    tmp = a[x1];
    a[x1] = a[x2];
    a[x2] = tmp;
  }
  return true;
}

// makes an Evaluator object
function makeEvaluator(expr)
{
  // checks the expression format
  if (!EXPRESSION_RE.test(expr)) {
    throw 'Invalid expression.';
  }

  // remove spaces
  expr = expr.replace(/ /g, '');
  
  // adds spaces around operators to get the expression in an easy-to-split format
  expr = expr.replace(/\+/g, ' + ');
  expr = expr.replace(/-/g, ' - ');
  expr = expr.replace(/\*/g, ' * ');
  expr = expr.replace(/\//g, ' / ');
   
  // builds the expression structure, an array of nodes representing numeric 
  // values or operators
  var exprStruct = [];
  var exprArray = expr.split(' ');
  var opsSet = {'+': true, '-': true, '*': true, '/': true};
  for (var i = 0; i < exprArray.length; i++) {
    var val = exprArray[i];
    if (val in opsSet) {
      exprStruct.push({op: val});
    } else {
      exprStruct.push({val: parseFloat(val), str: val.toString()});
    }
  }
  
  // returns the Evaluator object
  return {
    // expression structure
    _a: exprStruct,
    
    // returns the number of operators
    getNumOps: function() {
      return Math.floor(this._a.length / 2);
    },
    
    // returns the result, given the order of operations as a permutation of
    // [0, 1, 2, ..., number-of-operators - 1]
    getResult: function(order) {
      // gets the node that represents a given node
      function getRep(obj) {
        if (!('rep' in obj)) {
          return obj;
        } else {
          return obj.rep = getRep(obj.rep);
        }
      }
      
      // given a string representing the left operand, the last operation made
      // at the left operand, the same quantities associated with the right
      // operand and the current operand, returns a string associated with the
      // expression ('N' is the "operator" associated with a pure number)
      function addParens(lStr, lOp, rStr, rOp, op) {
        // just applies precedence rules, disambiguating with parentheses when
        // there are possible ambiguities
        if (op === '+') {
          return lStr + op + rStr;
        } else if (op === '-') {
          if (rOp === '+' || rOp === '-') {
            return lStr + op + '(' + rStr + ')';
          } else {
            return lStr + op + rStr;
          }
        } else if (op === '*') {
          if (lOp === '+' || lOp === '-' || lOp === '/') {
            lStr = '(' + lStr + ')';
          }
          if (rOp === '+' || rOp === '-' || rOp === '/') {
            rStr = '(' + rStr + ')';
          }
          return lStr + op + rStr;
        } else if (op === '/') {
          if (lOp !== 'N') {
            lStr = '(' + lStr + ')';
          }
          if (rOp !== 'N') {
            rStr = '(' + rStr + ')';
          }
          return lStr + op + rStr;
        } else {
          throw '';
        }
      }
      
      // cleans up the expression structure to do a new evaluation
      for (var i = 0; i < this._a.length; i++) {
        if ('rep' in this._a[i]) {
          delete this._a[i].rep;
        }
        if ('op' in this._a[i] && 'str' in this._a[i]) {
          delete this._a[i].str;
        }
        if ('op' in this._a[i] && 'val' in this._a[i]) {
          delete this._a[i].val;
        }
      }
      
      // checks if the order of operations array has the correct length
      if (order.length * 2 + 1 !== this._a.length) {
        throw 'Invalid order description.';
      }
      
      // does the operations in order
      for (var i = 0; i < order.length; i++) {
      
        // checks if this item of the order of operations array is in range
        if (order[i] < 0 || order[i] > order.length - 1) {
          throw 'Invalid order description.';
        }
        
        // checks if this operator is already processed
        if ('rep' in this._a[2*order[i]+1]) {
          throw 'Invalid order description.';
        }
        
        // gets the representative nodes of the left & right operands
        var lRep = getRep(this._a[2*order[i]]);
        var rRep = getRep(this._a[2*order[i]+2]);
        
        // gets the operator of the current node
        var op = this._a[2*order[i]+1].op;
        
        // gets the value of the current node from the value of the operands 
        // and the operator of the current node
        if (op === '+') {
          this._a[2*order[i]+1].val = lRep.val + rRep.val;
        } else if (op === '-') {
          this._a[2*order[i]+1].val = lRep.val - rRep.val;
        } else if (op === '*') {
          this._a[2*order[i]+1].val = lRep.val * rRep.val;
        } else if (op === '/') {
          this._a[2*order[i]+1].val = lRep.val / rRep.val;
        } else {
          throw 'INTERNAL ERROR.';
        }
        
        // gets the operators of the left & right operands, using 'N' if they 
        // are just numbers
        var lOp = ('op' in lRep) ? lRep.op : 'N';
        var rOp = ('op' in rRep) ? rRep.op : 'N';
        
        // gets the string representation of the expression associated with the
        // current node
        this._a[2*order[i]+1].str = addParens(lRep.str, lOp, rRep.str, rOp, op);
        
        // puts this node as representative of the other two
        lRep.rep = rRep.rep = this._a[2*order[i]+1];
      }
      
      // gets the representative node of the whole expression, once all the 
      // operations are done
      var rep = getRep(this._a[0]);
      
      // returns the value and the string representation of the whole 
      // expression
      return [rep.val, rep.str];
    }
  };
}

function parenthesize(expr, result)
{ 
  // it's a brute force solution, just checks all possible operation orders
  
  // makes an evaluator
  ev = makeEvaluator(expr);
  
  // converts the result to a numerical value
  result = parseFloat(result.replace(/ /g, ''));

  // initial operation order
  var order = [];
  for (var i = 0; i < ev.getNumOps(); i++) {
    order.push(i);
  }
  
  // solutions set
  var solutionsMap = {};
  
  // goes through all the permutations
  while (true) {
    
    // tries with the current permutation
    var res = ev.getResult(order);
    
    // if it gives the correct result, adds it to the set
    if (res[0] === result) {
      solutionsMap[res[1]] = true;
    }
    
    // gets the next permutation
    if (!updPerm(order)) {
      // exits if there are no more
      break;
    }
  }
  
  // builds the solutions array from the set
  var solutions = [];
  for (var sol in solutionsMap) {
    solutions.push(sol);
  }
  
  // returns the solutions array
  return solutions;
}
