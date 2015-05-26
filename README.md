# haskhol-haskell
HaskHOL libraries for Haskell reasoning, including a verification plugin.

## Overview
The plugin provided in the HaskHOL.Haskell.Plugin module is an implementation of the verification workflow I've been working on as part of my dissertation work.
Essentially, the plugin links HaskHOL into GHC at the intermediate language level, such that it can translate bindings to HOL terms and use the results to construct and prove proof obligations.

More information about the plugin can be found in one of my [draft papers](http://ecaustin.github.io/haskhol/papers/proof_plugin.pdf).

## Installation
In order to compile the HaskHOL-Haskell package and use this plugin, the following dependencies must be installed from GitHub:

* [HaskHOL-Core](../../../haskhol-core)
* [HaskHOL-Deductive](../../../haskhol-deductive)
* [HaskHOL-Math](../../../haskhol-math)
* [KURE](../../../../ku-fpg/kure)
* [HERMIT](../../../../ku-fpg/hermit)

The versions of the remaining dependencies that are available on Hackage should be fine.

## Execution
Once installed, there are a number of examples that have been pre-configured as a demonstration.
Each can be run by navigating to the desired directory and running the `make` command.
You should see notes about the steps that the plugin is taking, followed by a (not-so) pretty-printed theorem showing that the proof is complete.

Note that while the plugin is flexible in the sense that it works for these examples of varying type and construction, it is not yet flexible enough to scale to "real world" code.
That being said, if you have a particular example in mind you'd like to adapt the plugin for, I'd be happy to help or lend guidance as needed.
