import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFRepFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.WeightPositive

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def InW (D : Formalism.BasicNotions.D7) (y : (VS D).V) : Prop :=
  (∀ a, (VS D).hT (D.sp.hypE a) y = 0) ∧ (∀ a, (VS D).hT (D.sp.hypF a) y = 0) ∧ (VS D).hT D.sp.zm y = 0

theorem hT_star (D : Formalism.BasicNotions.D7) (x y : (VS D).V) : star ((VS D).hT x y) = (VS D).hT y x := by
  have h := (VS D).herm
  first
  | exact h x y
  | exact h.eq x y
  | simpa using h x y
  | simpa using h.eq x y

theorem T_ne (D : Formalism.BasicNotions.D7) : (D.sp.T : D.host.E) ≠ 0 := by
  have h := D.sp.T_prime.ne_zero
  exact_mod_cast h

theorem hZE (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT D.sp.zm (D.sp.hypE i) = 0 := by exact (D.sp.hyp_orthz i).1
theorem hZF (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT D.sp.zm (D.sp.hypF i) = 0 := by exact (D.sp.hyp_orthz i).2
theorem hEZ (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT (D.sp.hypE i) D.sp.zm = 0 := by
  rw [← hT_star D D.sp.zm (D.sp.hypE i), hZE, star_zero]
theorem hFZ (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT (D.sp.hypF i) D.sp.zm = 0 := by
  rw [← hT_star D D.sp.zm (D.sp.hypF i), hZF, star_zero]

def pWL (D : Formalism.BasicNotions.D7) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id - ∑ a, ((VS D).hT (D.sp.hypF a)).smulRight (D.sp.hypE a)
    - ∑ a, ((VS D).hT (D.sp.hypE a)).smulRight (D.sp.hypF a)
    + ((D.sp.T : D.host.E)⁻¹) • ((VS D).hT D.sp.zm).smulRight D.sp.zm

theorem pW_eq (D : Formalism.BasicNotions.D7) (v : (VS D).V) : pW D v = pWL D v := by
  simp only [pW, pWL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply, smul_smul, div_eq_inv_mul]

theorem pW_add (D : Formalism.BasicNotions.D7) (u v : (VS D).V) : pW D (u + v) = pW D u + pW D v := by simp only [pW_eq, map_add]
theorem pW_sub (D : Formalism.BasicNotions.D7) (u v : (VS D).V) : pW D (u - v) = pW D u - pW D v := by simp only [pW_eq, map_sub]
theorem pW_smul (D : Formalism.BasicNotions.D7) (k : D.host.E) (v : (VS D).V) : pW D (k • v) = k • pW D v := by simp only [pW_eq, map_smul]
theorem pW_sum (D : Formalism.BasicNotions.D7) {ι : Type} (s : Finset ι) (v : ι → (VS D).V) :
    pW D (∑ i ∈ s, v i) = ∑ i ∈ s, pW D (v i) := by simp only [pW_eq, map_sum]

private theorem hT_hypF_hypE (D : Formalism.BasicNotions.D7) (a i : Fin D.R.rS) :
    (VS D).hT (D.sp.hypF a) (D.sp.hypE i) = if a = i then 1 else 0 := by
  rw [← hT_star D (D.sp.hypE i) (D.sp.hypF a), D.sp.hyp_ef i a]
  by_cases h : a = i
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem pW_e (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : pW D (D.sp.hypE i) = 0 := by
  simp [pW, hT_hypF_hypE, D.sp.hyp_ee, hZE, ite_smul, Finset.sum_ite_eq']

theorem pW_inW (D : Formalism.BasicNotions.D7) {y : (VS D).V} (hy : InW D y) : pW D y = y := by
  unfold InW at hy
  obtain ⟨h1, h2, h3⟩ := hy
  simp [pW, h1, h2, h3]

theorem inW_pW (D : Formalism.BasicNotions.D7) (v : (VS D).V) : InW D (pW D v) := by
  have hT0 := T_ne D
  unfold InW
  refine ⟨fun b => ?_, fun b => ?_, ?_⟩
  · simp [pW, map_sum, D.sp.hyp_ee, D.sp.hyp_ef, hEZ, mul_ite, Finset.sum_ite_eq]
  · simp [pW, map_sum, hT_hypF_hypE, D.sp.hyp_ff, hFZ, mul_ite, Finset.sum_ite_eq']
  · simp [pW, map_sum, hZE, hZF, D.sp.zm_norm, div_mul_cancel₀, hT0]

def eichL (D : Formalism.BasicNotions.D7) (e y : (VS D).V) (c : D.host.E) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id + ((VS D).hT e).smulRight y - ((VS D).hT y).smulRight e + c • ((VS D).hT e).smulRight e

theorem eichL_apply (D : Formalism.BasicNotions.D7) (e y : (VS D).V) (c : D.host.E) (v : (VS D).V) :
    eichL D e y c v = v + (VS D).hT e v • y - (VS D).hT y v • e + (c * (VS D).hT e v) • e := by
  simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply, smul_smul]

theorem eich_inv (D : Formalism.BasicNotions.D7) {e y : (VS D).V} {c : D.host.E} (he : (VS D).hT e e = 0)
    (hey : (VS D).hT e y = 0) (hye : (VS D).hT y e = 0) (hc : c + c + (VS D).hT y y = 0) (v : (VS D).V) :
    eichL D e (-y) c (eichL D e y c v) = v := by
  have h1 : (VS D).hT e (eichL D e y c v) = (VS D).hT e v := by
    simp [eichL_apply, he, hey]
  have h2 : (VS D).hT y (eichL D e y c v) = (VS D).hT y v + (VS D).hT e v * (VS D).hT y y := by
    simp [eichL_apply, hye] <;> ring
  have hc' : (VS D).hT e v * (c + c + (VS D).hT y y) = 0 := by rw [hc, mul_zero]
  rw [eichL_apply D e (-y) c (eichL D e y c v), h1]
  simp only [map_neg, LinearMap.neg_apply, h2]
  rw [eichL_apply D e y c v]
  linear_combination (norm := module) hc' • e

theorem eich_isom (D : Formalism.BasicNotions.D7) {e y : (VS D).V} {c : D.host.E} (he : (VS D).hT e e = 0)
    (hey : (VS D).hT e y = 0) (hye : (VS D).hT y e = 0) (hc : c + star c + (VS D).hT y y = 0)
    (u v : (VS D).V) : (VS D).hT (eichL D e y c u) (eichL D e y c v) = (VS D).hT u v := by
  have hE : ∀ w, (VS D).hT e (eichL D e y c w) = (VS D).hT e w := fun w => by
    simp [eichL_apply, he, hey]
  have hY : ∀ w, (VS D).hT y (eichL D e y c w) = (VS D).hT y w + (VS D).hT e w * (VS D).hT y y := fun w => by
    simp [eichL_apply, hye] <;> ring
  have hU : ∀ w, (VS D).hT u (eichL D e y c w) = (VS D).hT u w + (VS D).hT e w * star ((VS D).hT y u)
      - (VS D).hT y w * star ((VS D).hT e u) + c * (VS D).hT e w * star ((VS D).hT e u) := fun w => by
    rw [hT_star D y u, hT_star D e u]
    simp [eichL_apply] <;> ring
  rw [eichL_apply D e y c u]
  simp only [map_add, map_sub, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hE, hY, hU, starRingEnd_apply, star_mul']
  linear_combination (star ((VS D).hT e u) * (VS D).hT e v) * hc

end PI.UnitaryGroupMassFormula.CntFormula
