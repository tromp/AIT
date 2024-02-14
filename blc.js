var fs = require('fs');
var data; // = ''; fs.readFileSync(0, 'utf-8');
var nchar = 0;
let bytemode = process.argv.length <= 2;
var nbit = 0;
var progchar;

function bit2lam(bit) {
  return function(x0) {
    return function(x1) {
        return bit ? x1 : x0
      }
  }
}

function byte2lam(bits,n) {
  return function(z) {
    return n-- ? z(bit2lam((bits>>n)&1))(byte2lam(bits,n)) // cons bitn bits>n
               : function(y) { return y }                                         // nil
  }
}

function input(n) {           // input from n'th character onward
  return function(z) {
    if (n >= data.length) {
      return function(y) { return y }     // nil
    }
    let c = data[n]; // cons charn chars>n
    return z(bytemode ? byte2lam(c,8) : bit2lam(c&1))(input(n+1))
  }
}

function lam2bit(lambit) {
  return lambit(function(){return 0})(function(){return 1})()  // force suspension
  // return lambit(0)(1);
}

function lam2byte(lambits, x) {
  return lambits(function(lambit) {
           y = 2*x + lam2bit(lambit);
           return function(lamtail) {
             return function() { return lam2byte(lamtail, y) }
           }
         })(String.fromCharCode(x))              // end of byte
}

function output(prog) {
  return prog(function(c) {      // more chars
    process.stdout.write(bytemode ? lam2byte(c,0) : lam2bit(c) ? '1' : '0');
    return function(tail) {
      return function() { return output(tail) }
    }
  })(42)                         // end of output
}

function getbit() {
  if (nbit==0) {
    progchar = data[nchar++];
    // console.log(progchar);
    nbit = bytemode ? 8 : 1;
  }
  let bit = (progchar >> --nbit) & 1;
  // process.stdout.write(bit?'1':'0');
  return bit;
}

function program() {
  if (getbit()) {               // variable
    var i = 0;
    while (getbit()==1) { i++ }
    return function() { return arguments[i] }
  } else if (getbit()) {        // application
    let p = program();
    let q = program();
    return function(...args) {
      return p(...args)(function(arg) { return q(...args)(arg) }) // suspend argument
      // return p(...args)(q(...args));
    }
  } else {
    let p = program();
    return function(...args) {
      return function(arg) { return p(arg, ...args) }  // extend environment with one more argument
    }
  }
}

id = function(x) { return x; }
nil = function(x) { return function(y) { return y; } }
cons = function(x) { return function(y) { return function(z) { return z(x)(y) } } }

process.stdin.on('readable', () => {
  if ((data = process.stdin.read()) != null) {
    prog = program()();
    output(prog(input(nchar)))             // run program with empty env on input
  }
});

// console.log(lam2byte(byte2lam(65,8),0));
// console.log(output(id(input(0))));
// output(input(0))             // run program with empty env on input

