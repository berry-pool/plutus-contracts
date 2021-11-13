<img src="./graphic.svg" width="100%">

The process consists of 3 scripts.
The first script is a minting policy that creates a one time thread token that is sent to a script output of the validator script.
The validator script is a state machine and increases a counter id after each mint.
The actual mint happens in a seperate minting policy. The mint only happens if the state machine successfully transitioned and the token name includes the correct counter id.
