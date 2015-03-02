# haskhol-haskell
HaskHOL libraries for Haskell reasoning, including a verification plugin.

# ICFP 2015
## Overview
The plugin provided in the HaskHOL.Haskell.Plugin module is an implementation of the verification workflow I've been working on as part of my dissertation work.
Essentially, the plugin links HaskHOL into GHC at the intermediate language level, such that it can translate bindings to HOL terms and use the results to construct and prove proof obligations.

More information about the plugin can be found in our [draft submission for ICFP'15](http://ecaustin.github.io/haskhol/papers/proof_plugin.pdf).

## Installation
In order to compile the HaskHOL-Haskell package and use this plugin, the following dependencies must be installed from GitHub:

* [HaskHOL-Core](../../../haskhol-core)
* [HaskHOL-Deductive](../../../haskhol-deductive)
* [HaskHOL-Math](../../../haskhol-math)
* [KURE](../../../../ku-fpg/kure)
* [HERMIT](../../../../ku-fpg/hermit)

The versions of the remaining dependencies that are available on Hackage should be fine.

## Execution
Once installed, navigate to the examples directory and run the following command:
> ghc Monad.hs -O2 -fforce-recomp -fplugin=HaskHOL.Haskell.Plugin

This should compile the Monad module and run the example verification.

Note that a number of critical values are hard-coded in this plugin, so it will currently only work for the provided module as is.
It is our intention to provide a more general plugin, as well as a number of other examples, ASAP.
