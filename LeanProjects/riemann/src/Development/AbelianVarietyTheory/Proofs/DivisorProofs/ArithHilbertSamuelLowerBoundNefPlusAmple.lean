import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountRadiusOneLowerBoundAmpleSemiPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorOfNefFibresAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundAlongResidues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOnFiniteFieldFibresPowTens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveNonnegCombination
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem lowerBound_along_div : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (c n : ℕ) (α : ℝ), 0 < n → NefFib P.L → P.L.SemiPos D → IsAmpleLB P.A.B → P.A.SemiPos D → ((P.L.pow n).tens P.A).IsSelfInter α → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (α / (D + 1).factorial / (n : ℝ) ^ (D + 1) - ε) * (M : ℝ) ^ (D + 1) ≤ P.lc M ((M / n : ℕ) - c) 1 := by
  intro _ hHS k _ X _ p D hX P c n α hn hL hLs hA hAs hα ε hε
  have : Module.Finite ℤ k := hX.finite
  have hp : IsProjOver p := hX.isProjOver
  have hLn : NefFib (P.L.pow n) := fun Z i _ _ κ _ _ _ hd => by
    rw [NefHodgeTateAt.topSelf_pow hp P.L n Z i κ hd]
    exact mul_nonneg (Nat.cast_nonneg _) (hL Z i κ hd)
  have hAmp : IsAmpleLB ((P.L.pow n).tens P.A).B := GlobalTheory.T.isAmple_tensor_of_nef_fibres_ample k X p D hX _ _ hLn hA
  have hSP : ((P.L.pow n).tens P.A).SemiPos D := (hLs.pow n).tens hAs
  have hRep : P.Rep (n : ℤ) 1 ((P.L.pow n).tens P.A) := by
    have h1 := Pair.rep_pow k X p P 1 0 P.L n (Pair.rep_base k X p P).1
    have h2 := Pair.rep_tens k X p P _ _ 0 1 _ _ h1 (Pair.rep_base k X p P).2.1
    simpa using h2
  refine lowerBound_along_residues (D + 1) n (fun M => P.lc M ((M / n : ℕ) - c) 1) (α / (D + 1).factorial) hn
    (fun r hr ε' hε' => ?_) ε hε
  filter_upwards [GlobalTheory.T.log_count_radius_one_lower_bound_ample_semiPos hHS k X p D hX P n 1 r (-(c : ℤ)) _ α hRep hAmp hSP hα ε' hε'] with q hq
  have e : (n * q + r) / n = q := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hr, zero_add]
  simp only [e]
  convert hq using 2 <;> push_cast <;> ring

end GlobalTheory.HSNef
