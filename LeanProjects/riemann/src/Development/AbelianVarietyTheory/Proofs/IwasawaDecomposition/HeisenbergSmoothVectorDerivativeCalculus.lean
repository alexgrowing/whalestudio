import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift.DCalc

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem hasDerivAt_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : V → E} (hF : Differentiable ℝ F)
    (w y : V) : HasDerivAt (fun t : ℝ => F (w + t • y)) (fderiv ℝ F w y) 0 := by
  have hl : HasDerivAt (fun t : ℝ => w + t • y) y 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const y).const_add w
  have hF' : HasFDerivAt F (fderiv ℝ F w) (w + (0 : ℝ) • y) := by
    simpa using (hF w).hasFDerivAt
  exact hF'.comp_hasDerivAt (0 : ℝ) hl

theorem hasDerivAt_lin (a : ℝ) : HasDerivAt (fun t : ℝ => (π * I * ((t * a : ℝ) : ℂ))) (π * I * a) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => ((t * a : ℝ) : ℂ)) (a : ℂ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const a).ofReal_comp
  exact h1.const_mul (π * I)

theorem hasDerivAt_phase (a : ℝ) {G : ℝ → B} {G' : B} (hG : HasDerivAt G G' 0) :
    HasDerivAt (fun t : ℝ => cexp (π * I * ((t * a : ℝ) : ℂ)) • G t) (G' + (π * I * a : ℂ) • G 0) 0 := by
  have hc := (hasDerivAt_lin a).cexp
  have hp : HasDerivAt (fun t : ℝ => cexp (π * I * ((t * a : ℝ) : ℂ)) • G t) _ 0 := hc.smul hG
  convert hp using 1
  simp

variable {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B}

theorem skew (h0 : ∀ x, om x x = 0) (x y : V) : om y x = -om x y := by
  have hxy := h0 (x + y)
  simp only [map_add, _root_.add_apply, h0] at hxy
  linarith

theorem heis_dH (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (w y : V) :
    ρ w (dH ρ y f) = fderiv ℝ (fun u => ρ u f) w y + (π * I * (om w y : ℂ)) • ρ w f := by
  have hd : Differentiable ℝ (fun u => ρ u f) :=
    (show ContDiff ℝ ∞ (fun u => ρ u f) from hf).differentiable (by simp)
  have h1 : HasDerivAt (fun t : ℝ => ρ w (ρ (t • y) f)) (ρ w (dH ρ y f)) 0 := by
    have hl := hasDerivAt_dH y hf
    exact ((ρ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
  have h2 : HasDerivAt (fun t : ℝ => ρ w (ρ (t • y) f))
      (fderiv ℝ (fun u => ρ u f) w y + (π * I * (om w y : ℂ)) • ρ w f) 0 := by
    have hp := hasDerivAt_phase (om w y) (hasDerivAt_line hd w y)
    convert hp using 1
    · funext t
      rw [h.2.1]
      simp
    · simp
  exact h1.unique h2

theorem sm_heis (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (w : V) : Sm ρ (ρ w f) := by
  have hf' : ContDiff ℝ ∞ (fun u => ρ u f) := hf
  have e : (fun u => ρ u (ρ w f)) = fun u => cexp (π * I * (om u w : ℂ)) • ρ (u + w) f := by
    funext u
    exact h.2.1 u w f
  show ContDiff ℝ ∞ (fun u => ρ u (ρ w f))
  rw [e]
  apply ContDiff.smul
  · apply ContDiff.cexp
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (om.contDiff.clm_apply contDiff_const))
  · exact hf'.comp (contDiff_id.add contDiff_const)

theorem contDiff_fderiv {f : B} (hf : Sm ρ f) : ContDiff ℝ ∞ (fderiv ℝ fun u => ρ u f) := (contDiff_infty_iff_fderiv.1 (show ContDiff ℝ ∞ (fun u => ρ u f) from hf)).2

theorem sm_dH (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (v : V) : Sm ρ (dH ρ v f) := by
  have hf' : ContDiff ℝ ∞ (fun u => ρ u f) := hf
  have e : (fun u => ρ u (dH ρ v f)) =
      fun u => fderiv ℝ (fun u => ρ u f) u v + (π * I * (om u v : ℂ)) • ρ u f := by
    funext u
    exact heis_dH h hf u v
  show ContDiff ℝ ∞ (fun u => ρ u (dH ρ v f))
  rw [e]
  refine ((contDiff_fderiv hf).clm_apply contDiff_const).add ?_
  exact (contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp (om.contDiff.clm_apply contDiff_const))).smul hf'

theorem dH_heis (h0 : ∀ x, om x x = 0) (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (v w : V) :
    dH ρ v (ρ w f) = ρ w (dH ρ v f) + (2 * π * I * (om v w : ℂ)) • ρ w f := by
  have hd : Differentiable ℝ (fun u => ρ u f) :=
    (show ContDiff ℝ ∞ (fun u => ρ u f) from hf).differentiable (by simp)
  have h1 := hasDerivAt_dH v (sm_heis h hf w)
  have h2 : HasDerivAt (fun t : ℝ => ρ (t • v) (ρ w f))
      (fderiv ℝ (fun u => ρ u f) w v + (π * I * (om v w : ℂ)) • ρ w f) 0 := by
    have hp := hasDerivAt_phase (om v w) (hasDerivAt_line hd w v)
    convert hp using 1
    · funext t
      rw [h.2.1, add_comm (t • v) w]
      simp
    · simp
  rw [h1.unique h2, heis_dH h hf w v, skew h0 w v, add_assoc, ← add_smul]
  congr 2
  push_cast
  ring

theorem dH_dH (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (u v : V) :
    dH ρ u (dH ρ v f) = fderiv ℝ (fderiv ℝ fun u => ρ u f) 0 u v + (π * I * (om u v : ℂ)) • f := by
  have hd2 : Differentiable ℝ (fderiv ℝ fun u => ρ u f) :=
    (contDiff_fderiv hf).differentiable (by simp)
  have h1 := hasDerivAt_dH u (sm_dH h hf v)
  have hA : HasDerivAt (fun t : ℝ => fderiv ℝ (fun u => ρ u f) (0 + t • u) v)
      (fderiv ℝ (fderiv ℝ fun u => ρ u f) 0 u v) 0 := by
    have hl := (hasDerivAt_line hd2 0 u).clm_apply (hasDerivAt_const (0 : ℝ) v)
    simpa using hl
  have hB := (hasDerivAt_lin (om u v)).smul (hasDerivAt_dH u hf)
  have h2 := hA.add hB
  have e : (fun t : ℝ => ρ (t • u) (dH ρ v f)) = fun t : ℝ =>
      fderiv ℝ (fun u => ρ u f) (0 + t • u) v + (π * I * ((t * om u v : ℝ) : ℂ)) • ρ (t • u) f := by
    funext t
    rw [heis_dH h hf]
    simp
  rw [e] at h1
  rw [h1.unique h2]
  simp [h.1]

theorem dH_commutator (h0 : ∀ x, om x x = 0) (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (u v : V) :
    dH ρ u (dH ρ v f) - dH ρ v (dH ρ u f) = (2 * π * I * (om u v : ℂ)) • f := by
  have hf' : ContDiff ℝ ∞ (fun u => ρ u f) := hf
  have hs : IsSymmSndFDerivAt ℝ (fun u => ρ u f) 0 := hf'.contDiffAt.isSymmSndFDerivAt
    (by simpa using (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)))
  rw [dH_dH h hf u v, dH_dH h hf v u, hs v u, skew h0 u v, add_sub_add_left_eq_sub, ← sub_smul]
  congr 1
  push_cast
  ring

theorem dH_calculus : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ f, Sm ρ f → (∀ v, Sm ρ (dH ρ v f)) ∧ (∀ w, Sm ρ (ρ w f)) ∧ (∀ w y, fderiv ℝ (fun u => ρ u f) w y = ρ w (dH ρ y f) - (π * I * (om w y : ℂ)) • ρ w f) ∧ (∀ v w, dH ρ v (ρ w f) = ρ w (dH ρ v f) + (2 * π * I * (om v w : ℂ)) • ρ w f) ∧ ∀ u v, dH ρ u (dH ρ v f) - dH ρ v (dH ρ u f) = (2 * π * I * (om u v : ℂ)) • f := by
  intro V _ _ B _ _ om ρ h0 h f hf
  exact ⟨fun v => sm_dH h hf v, fun w => sm_heis h hf w,
    fun w y => eq_sub_of_add_eq (heis_dH h hf w y).symm, fun v w => dH_heis h0 h hf v w,
    fun u v => dH_commutator h0 h hf u v⟩

end GlobalTheory.Mem.Lift.DCalc
