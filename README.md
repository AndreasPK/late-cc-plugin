The simplest set up for working on a plugin.

To build the plugin

```
cabal new-build plugin
```

To test the plugin

```
cabal new-test test
```

# Using the LateCCPlugin

To use the plugin on a package:
* Add the plugin as a dependecy to the package like any other package.
* Enable profiling and disable automatic insertion of cost centres:
```
profiling: true
```
* Add a ghc option to enable the plugin for the package: `ghc-options: -fplugin=LateCCPlugin`

And that's it! This will disable the default method of const centre insertion and instead insert
cost centres at the end of the compilation pipeline.