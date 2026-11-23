import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.OneMemSecAndSecInfEqBot
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.SecRingNonZeroDiv

open GlobalTheory.CompHt GlobalTheory.FlagTan

theorem eq_zero_of_mul_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (e : Ix Dw → ℤ) (F : Rul Xo c), F ∈ secZ Xo c e → (∀ Z : Comp Xo c, ∃ y : FrPt Xo c ℂ, LiesOn Z y ∧ evR Xo c F y ≠ 0) → ∀ f ∈ secRing Xo c, F * f = 0 → f = 0 := by
  intro E _ _ _ H Dw l Xo c e F hF hZ f hf hFf
  classical
  have hG : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  have hFZ : ∀ Z : Comp Xo c, genVal Z F ≠ 0 := by
    intro Z h0
    obtain ⟨y, hy, hne⟩ := hZ Z
    exact hne ((genVal_eq_zero_iff E H Dw l Xo c Z e F hF).1 h0 ℂ y hy)
  have hf' : f ∈ ⨆ e, secZ Xo c e := by rw [← GlobalTheory.LevDesc.toSubmodule_secRing]; exact hf
  obtain ⟨a, ha, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ f).1 hf'
  have key : ∀ Z : Comp Xo c, ∀ d ∈ a.support, genVal Z (a d) = 0 := by
    intro Z
    haveI : CharZero (Om Z) := charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
    let χ : (Ix Dw → ℤ) → ((Ix Dw → (Om Z)ˣ) →* Om Z) := fun d =>
      { toFun := fun t => ((∏ i, t i ^ d i : (Om Z)ˣ) : Om Z)
        map_one' := by simp
        map_mul' := fun t s => by simp [mul_zpow, Finset.prod_mul_distrib] }
    have hχ : Function.Injective χ := by
      intro d d' hdd
      funext i
      let u : (Om Z)ˣ := Units.mk0 2 two_ne_zero
      have hp : ∀ d : Ix Dw → ℤ, χ d (Pi.mulSingle i u) = (2 : Om Z) ^ d i := by
        intro d
        show ((∏ j, (Pi.mulSingle i u : Ix Dw → (Om Z)ˣ) j ^ d j : (Om Z)ˣ) : Om Z) = _
        rw [Finset.prod_eq_single i]
        · simp [u, Units.val_zpow_eq_zpow_val]
        · intro j _ hj
          simp [Pi.mulSingle_eq_of_ne hj]
        · simp
      have h1 : (2 : Om Z) ^ d i = (2 : Om Z) ^ d' i := by
        rw [← hp, ← hp, hdd]
      have h2 : (((2 : ℚ) ^ d i : ℚ) : Om Z) = (((2 : ℚ) ^ d' i : ℚ) : Om Z) := by
        rw [Rat.cast_zpow, Rat.cast_zpow, Rat.cast_ofNat]; exact h1
      exact zpow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num) (Rat.cast_injective h2)
    have hli : LinearIndependent (Om Z) (fun d => (χ d : (Ix Dw → (Om Z)ˣ) → Om Z)) :=
      (linearIndependent_monoidHom _ (Om Z)).comp χ hχ
    have hsum : ∑ d ∈ a.support, genVal Z (a d) • (χ d : (Ix Dw → (Om Z)ˣ) → Om Z) = 0 := by
      funext t
      obtain ⟨y', hy'⟩ := SecSeparation.exists_frBor (genFr hG Z) t
      have h1 : evR Xo c (F * a.sum fun _ x => x) y' = 0 := by rw [hFf]; exact evalAt_zero _ _ y'
      have h2 : evR Xo c (F * a.sum fun _ x => x) y' = evR Xo c F y' * evR Xo c (a.sum fun _ x => x) y' :=
        evalAt_mul _ _ _ _ y'
      have h3 : evR Xo c F y' ≠ 0 := by
        rw [evR_frBor hF hy']
        exact mul_ne_zero (Units.ne_zero _) (hFZ Z)
      have h4 : evR Xo c (a.sum fun _ x => x) y' = 0 := (mul_eq_zero.1 (h2.symm.trans h1)).resolve_left h3
      have h5 : evR Xo c (a.sum fun _ x => x) y' = ∑ d ∈ a.support, evR Xo c (a d) y' :=
        map_sum (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y') _ _
      rw [h5] at h4
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h4]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [evR_frBor (ha d) hy', mul_comm]
      rfl
    intro d hd
    exact linearIndependent_iff'.1 hli a.support (fun d => genVal Z (a d)) hsum d hd
  refine Finset.sum_eq_zero fun d hd => ?_
  exact secZ_eq_zero_of_genVal (ha d) fun Z => key Z d hd

end GlobalTheory.SecRingNonZeroDiv
