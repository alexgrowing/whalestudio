import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionIffExistsSmallSectionDiffeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundleDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem le_of_rep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (a b a' b' : ℤ) (M M' : HermLB p) (f : X.functionField), P.Rep a b M → P.Rep a' b' M' → f ≠ 0 → f ∈ P.Bl (a - a') (b - b') 1 → Le M' M := by
  intro k _ X _ p P a b a' b' M M' f hM hM' hf hB
  have hR : P.Rep (a - a') (b - b') (M.tens M'.dual) := by
    have h := Pair.rep_tens k X p P a b (-a') (-b') M M'.dual hM (Pair.rep_dual k X p P a' b' M' hM')
    simpa only [sub_eq_add_neg] using h
  obtain ⟨e, -, hrange, hnorm, hloc⟩ := RepDict.rep_dict k X p P _ _ _ hR
  have hfH : f ∈ (P.H (a - a') (b - b') : Set X.functionField) := hB.1
  rw [← hrange] at hfH
  obtain ⟨u, rfl⟩ := hfH
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_exists_smallSection_difference k X p M M').2 ⟨u, fun σ y => ?_, fun hu => ?_⟩
  · rw [← hnorm u σ y]
    have h0 : 0 ≤ P.nu (a - a') (b - b') σ y (e u) := by
      unfold Pair.nu; positivity
    exact pow_le_one₀ h0 (hB.2 σ y)
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (P.L.isLB.cover.ge (Opens.mem_top (genericPoint X)))
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (P.A.isLB.cover.ge (Opens.mem_top (genericPoint X)))
    have hne : P.loc (a - a') (b - b') (e u) i j ≠ 0 := by
      have h1 := (P.r i).ne_zero
      have h2 := (P.r' j).ne_zero
      simp only [Pair.loc]
      exact mul_ne_zero (mul_ne_zero hf (zpow_ne_zero _ h1)) (zpow_ne_zero _ h2)
    have hg := (hloc u (genericPoint X) i j hi hj).2 (unitAt_genericPoint hne)
    obtain ⟨c, hc⟩ := Opens.mem_iSup.1 ((M.tens M'.dual).isLB.cover.ge (Opens.mem_top (genericPoint X)))
    rw [mem_nonzeroLocus_iff u c hc, hu] at hg
    change genericPoint X ∈ X.basicOpen (0 : Γ(X, _)) at hg
    simp at hg

end GlobalTheory.HSNef
