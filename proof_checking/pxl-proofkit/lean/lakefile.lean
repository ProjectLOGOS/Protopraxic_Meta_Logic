import Lake
open Lake

package «pxlv3» where
  -- no extra config

@[default_target]
lean_lib PXLv3

require std from git
  "https://github.com/leanprover/std4" @ "v0.6.0"
