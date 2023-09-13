import Lake
open Lake DSL

package «infinite_primes» {
  -- add package configuration options here
}

lean_lib «InfinitePrimes» {
  -- add library configuration options here
}

@[default_target]
lean_exe «infinite_primes» {
  root := `Main
}
