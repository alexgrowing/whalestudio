import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PDivGroup

open GlobalTheory.PDiv

theorem eq_zero_of_cob_eq_zero_of_pow (p : ℕ) (R : Type) [CommRing R] (N : ℕ)
    (hN : (p : R) ^ N = 0) (G : PDivGroup p R) (B : G.funs) (hB : G.cob B = 0) : B = 0 := by
  have key : ∀ k : ℕ, (∀ n, mulBy R (G.A n) (p ^ k) (B.1 n) = 0) → ∀ n, B.1 n = 0 := by
    intro k
    induction k with
    | zero =>
      intro h n
      have h1 := (mulBy_of_cobOne_eq_zero (congrArg (fun x : G.cocycles => x.1 n) hB) (p ^ 0)).1
      rw [h n, pow_zero, one_smul] at h1
      exact h1.symm
    | succ k ih =>
      intro h
      refine ih fun n => Test.mulP_injective G n ?_
      rw [map_zero, map_mulBy, ← B.2 n, mulP_res, mulBy_mulBy, ← pow_succ, h]
  refine Subtype.ext (funext (key N fun n => ?_))
  rw [(mulBy_of_cobOne_eq_zero (congrArg (fun x : G.cocycles => x.1 n) hB) (p ^ N)).1,
    ← Nat.cast_smul_eq_nsmul R, Nat.cast_pow, hN, zero_smul]

end GlobalTheory.PDivGroup
