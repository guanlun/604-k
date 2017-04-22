/**
 * Run "npm install pretty-data" first
 * Sample use: node krun-pretty.js --debugger test.imp
 */

'use strict';

const pd = require('pretty-data').pd;
const spawn = require('child_process').spawn;

const child = spawn('krun', process.argv.slice(2));

let output = '';

child.stdout.on('data', chunk => {
    output += chunk.toString();
});

child.stderr.on('data', chunk => {
    output += chunk.toString();
});

process.stdin.on('data', data => {
    child.stdin.write(data);
});

setInterval(() => {
    if (output !== '') {
        process.stdout.write(pd.xml(output));
        output = '';
    }
}, 100);