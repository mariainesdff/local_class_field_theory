import blueprint_tests
import complete_dvr
import global_to_local
import local_field
import normalized_valuation
import old_padic
import spectral_norm
import discrete_valuation_ring.basic
import discrete_valuation_ring.extensions
import discrete_valuation_ring.global_to_local
import eq_characteristic.basic
import eq_characteristic.valuation
import for_mathlib.algebra_comp
import for_mathlib.normed_valued
import for_mathlib.num_denom_away
import for_mathlib.polynomial
import for_mathlib.power_series
import for_mathlib.rank_one_valuation
import for_mathlib.residue_ring_def
import for_mathlib.laurent_series_iso.power_series_adic_completion
import for_mathlib.laurent_series_iso.second_try
import from_mathlib.alg_norm_of_galois
import from_mathlib.Cp_def
import from_mathlib.filter
import from_mathlib.limsup
import from_mathlib.minpoly
import from_mathlib.normal_closure
import from_mathlib.normed_space
import from_mathlib.normed_valued
import from_mathlib.pow_mult_faithful
import from_mathlib.rank_one_valuation
import from_mathlib.ring_seminorm
import from_mathlib.seminorm_from_bounded
import from_mathlib.seminorm_from_const
import from_mathlib.smoothing_seminorm
import from_mathlib.spectral_norm
import from_mathlib.spectral_norm_unique
import mixed_characteristic.basic
import mixed_characteristic.valuation
import data.list.sort meta.expr system.io

open tactic declaration environment io io.fs (put_str_ln close)

-- The next instance is there to prevent PyYAML trying to be too smart
meta def my_name_to_string : has_to_string name :=
⟨λ n, "\"" ++ to_string n ++ "\""⟩

local attribute [instance] my_name_to_string

meta def pos_line (p : option pos) : string :=
match p with
| some x := to_string x.line
| _      := ""
end

meta def file_name (p : option string) : string :=
match p with
| some x := x
| _      := ""
end

meta def print_item_crawl (env : environment) (h : handle) (decl : declaration) : io unit :=
let name := decl.to_name in
do
   put_str_ln h ((to_string name) ++ ":"), 
   put_str_ln h  ("  File: " ++ file_name (env.decl_olean name)),
   put_str_ln h ("  Line: " ++ pos_line (env.decl_pos name))

/-- itersplit l n will cut a list l into 2^n pieces (not preserving order) -/
meta def itersplit {α} : list α → ℕ → list (list α)
| l 0 := [l]
| l 1 := let (l1, l2) := l.split in [l1, l2]
| l (k+2) := let (l1, l2) := l.split in itersplit l1 (k+1) ++ itersplit l2 (k+1)

meta def main : io unit :=
do curr_env ← run_tactic get_env,
   h ← mk_file_handle "decls.yaml" mode.write,
   let decls := curr_env.fold [] list.cons,
   let filtered_decls := decls.filter
     (λ x, not (to_name x).is_internal),
   let pieces := itersplit filtered_decls 5,
   pieces.mmap' (λ l, l.mmap' (print_item_crawl curr_env h)),
   close h
