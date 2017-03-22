const exec = require('child_process').exec;

function processCommand(path) {
    exec(`krun --debugger ${path}`, (err, stdout, stderr) => {
        console.log(stdout);
    });
}

const targetFile = process.argv[2];

if (targetFile) {
    processCommand(targetFile);
} else {
    console.log("Invalid args");
}
