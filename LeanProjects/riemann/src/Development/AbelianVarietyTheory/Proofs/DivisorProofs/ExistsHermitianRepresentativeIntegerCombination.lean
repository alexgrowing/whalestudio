import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundleDual
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

theorem GlobalTheory.VolBr.Pair.exists_rep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (P : Pair p) (a b : ℤ), ∃ M : HermLB p, P.Rep a b M := by
  intro k _ X _ p P a b
  obtain ⟨hL, hA, -⟩ := Pair.rep_base k X p P
  have cast (x y x' y' : ℤ) (M : HermLB p) (h : P.Rep x y M) (hx : x = x') (hy : y = y') :
      P.Rep x' y' M := by subst hx; subst hy; exact h
  have hLa := Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_pow k X p P _ _ _ a.toNat hL)
    (Pair.rep_dual k X p P _ _ _ (Pair.rep_pow k X p P _ _ _ (-a).toNat hL))
  have hAb := Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_pow k X p P _ _ _ b.toNat hA)
    (Pair.rep_dual k X p P _ _ _ (Pair.rep_pow k X p P _ _ _ (-b).toNat hA))
  refine ⟨_, cast _ _ _ _ _ (Pair.rep_tens k X p P _ _ _ _ _ _ hLa hAb) ?_ ?_⟩
  · have h1 := Int.toNat_sub_toNat_neg a
    simp only [mul_one, mul_zero, neg_zero, add_zero]
    omega
  · have h1 := Int.toNat_sub_toNat_neg b
    simp only [mul_one, mul_zero, neg_zero, zero_add]
    omega
