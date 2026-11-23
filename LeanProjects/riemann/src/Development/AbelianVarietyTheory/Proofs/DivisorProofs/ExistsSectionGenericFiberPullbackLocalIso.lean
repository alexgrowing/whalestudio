import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open GlobalTheory.ArInt

set_option autoImplicit false
noncomputable section

theorem GlobalTheory.Mix.exists_sec_bc : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral G] [IsLocallyNoetherian G] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ), (∀ x, IsIso (j.stalkMap x)) → ∀ (M : MLine p (τ.comp (algebraMap k K))) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), j (genericPoint G) = genericPoint X → ∃ (s' : (M.bc hp.w τ).B.Sec) (hs' : genericPoint G ∈ nonzeroLocus s'), nonzeroLocus s' = j ⁻¹ᵁ nonzeroLocus s ∧ (∀ x, (divOfSec (M.bc hp.w τ).φ.isLB s' hs').mult x = (divOfSec M.φ.isLB s hs).mult (j x)) ∧ ∀ y, (M.bc hp.w τ).logSec s' y = M.logSec s (bcPt hp.w τ y) := by
  intro k K _ _ _ _ X G _ _ _ _ p q j hp τ hiso M s hs hj
  let s' : (M.bc hp.w τ).B.Sec := Cartier.secPull s j
  have hnz : nonzeroLocus s' = j ⁻¹ᵁ nonzeroLocus s := Cartier.nonzeroLocus_secPull s j
  have hs' : genericPoint G ∈ nonzeroLocus s' := by
    rw [hnz]
    show j (genericPoint G) ∈ nonzeroLocus s
    rw [hj]
    exact hs
  refine ⟨s', hs', hnz, fun x => ?_, fun y => ?_⟩
  · have := hiso x
    let e : X.presheaf.stalk (j x) ≃+* G.presheaf.stalk x :=
      (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
    have hc : Order.coheight x = Order.coheight (j x) := by
      have := ringKrullDim_eq_of_ringEquiv e
      rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at this
      exact_mod_cast this.symm
    by_cases h1 : Order.coheight x = 1
    swap
    · rw [not_not.1 (mt CartierDiv.coheight_eq_one_of_mult_ne_zero h1),
        not_not.1 (mt CartierDiv.coheight_eq_one_of_mult_ne_zero (hc ▸ h1))]
    obtain ⟨i, hi⟩ := Geo.Tor.exists_chart M.φ.isLB (j x)
    have h₁ : x ∈ (M.bc hp.w τ).B.U fun _ => i := Set.mem_iInter.2 fun _ => hi
    rw [mult_divOfSec h1 h₁, mult_divOfSec (hc ▸ h1) hi]
    have hg : G.presheaf.germ _ x h₁ (s'.f fun _ => i) =
        j.stalkMap x (X.presheaf.germ _ _ hi (s.f i)) := by
      rw [Scheme.Hom.germ_stalkMap_apply]
      exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [hg]
    exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) (ord_map_ringEquiv e _)
  · have hy := mem_pick M.φ.isLB (bcPt hp.w τ y)
    have hy' : y ∈ ptsIn q τ ((M.bc hp.w τ).B.U fun _ => pick M.φ.isLB (bcPt hp.w τ y)) := by
      exact mem_ptsIn.2 (Set.mem_iInter.2 fun _ => mem_ptsIn.1 hy)
    have e1 : secVal q τ s' (fun _ => pick M.φ.isLB (bcPt hp.w τ y)) y =
        secVal p (τ.comp (algebraMap k K)) s (pick M.φ.isLB (bcPt hp.w τ y)) (bcPt hp.w τ y) := by
      exact (ev_res (Cartier.pull_U M.B j _).le hy' _).trans (valR_comp y.1 j _ _).symm
    simp only [MLine.logSec]
    rw [Weight.nsq_eq _ (secVal_mem s') hy', e1]
    simp [MLine.bc, Weight.linComb, Weight.nsq]
