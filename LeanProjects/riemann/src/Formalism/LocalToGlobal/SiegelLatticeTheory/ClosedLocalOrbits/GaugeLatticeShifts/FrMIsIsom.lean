import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NGClosed

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

variable {n r k : ℕ} {ε : Fin n → Bool} {e p : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℝ}

theorem hJ_syn_syn {w : Fin k → Fin n → ℂ} (F : Frm ε e p z w T) (α β : Fin r → ℂ) (γ : ℂ) (δ : Fin k → ℂ)
    (α' β' : Fin r → ℂ) (γ' : ℂ) (δ' : Fin k → ℂ) :
    hJ ε (syn e p z w T α β γ δ) (syn e p z w T α' β' γ' δ') =
      ∑ a, α' a * conj (β a) + ∑ a, β' a * conj (α a) + (-γ' / (T : ℂ)) * conj γ + ∑ j, δ' j * conj (δ j) := by
  rw [hJ_syn]
  have h1 : ∀ a, hJ ε (syn e p z w T α β γ δ) (e a) = conj (β a) := fun a => by rw [UnitaryIsometries.hJ_conj, syn_e F]
  have h2 : ∀ a, hJ ε (syn e p z w T α β γ δ) (p a) = conj (α a) := fun a => by rw [UnitaryIsometries.hJ_conj, syn_p F]
  have h3 : hJ ε (syn e p z w T α β γ δ) z = conj γ := by rw [UnitaryIsometries.hJ_conj, synthesized_vector_z_pairing F]
  have h4 : ∀ j, hJ ε (syn e p z w T α β γ δ) (w j) = conj (δ j) := fun j => by rw [UnitaryIsometries.hJ_conj, syn_w F]
  simp only [h1, h2, h3, h4]

def frL (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w y : Fin k → Fin n → ℂ) (T : ℝ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun v := syn e p z y T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v)
  map_add' v v' := by
    simp only [syn, UnitaryIsometries.hJ_add_right, add_smul, Finset.sum_add_distrib, neg_add, add_div]
    abel
  map_smul' c v := by
    simp only [syn, UnitaryIsometries.hJ_smul_right, RingHom.id_apply, smul_add, Finset.smul_sum, smul_smul]
    rw [show -(c * hJ ε z v) / (T : ℂ) = c * (-hJ ε z v / T) by ring]

def frM (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w y : Fin k → Fin n → ℂ) (T : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (frL (ε := ε) e p z w y T)

theorem frM_apply (w y : Fin k → Fin n → ℂ) (v : Fin n → ℂ) :
    frM (ε := ε) e p z w y T *ᵥ v =
      syn e p z y T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v) := by
  rw [frM, LinearMap.toMatrix'_mulVec]
  rfl

theorem frM_isIsom {w y : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (Fy : Frm ε e p z y T)
    (hdim : n = 2 * r + 1 + k) : UnitaryIsometries.IsIsom ε (frM (ε := ε) e p z w y T) := by
  intro v v'
  rw [frM_apply, frM_apply, hJ_syn_syn Fy]
  conv_rhs => rw [recon Fw hdim v, recon Fw hdim v', hJ_syn_syn Fw]

theorem frM_fix {w y : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k) {v : Fin n → ℂ}
    (hv : ∀ j, hJ ε (w j) v = 0) : frM (ε := ε) e p z w y T *ᵥ v = v := by
  rw [frM_apply]
  conv_rhs => rw [recon Fw hdim v]
  simp only [syn, hv, zero_smul, Finset.sum_const_zero]

theorem frM_w {w y : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (j : Fin k) :
    frM (ε := ε) e p z w y T *ᵥ w j = y j := by
  rw [frM_apply]
  simp only [syn, Fw.pw, Fw.ew, Fw.zw, Fw.ww, zero_smul, Finset.sum_const_zero, zero_add, neg_zero, zero_div,
    ite_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem span_perp {w : Fin k → Fin n → ℂ} (F : Frm ε e p z w T) (a : ℕ) :
    ∀ x ∈ spanLt e a, ∀ j, hJ ε x (w j) = 0 := by
  intro x hx j
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, _, rfl⟩ := hy
    exact F.ew b j
  | zero => exact UnitaryIsometries.hJ_zero_left ε _
  | add x y _ _ hx hy => rw [UnitaryIsometries.hJ_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [UnitaryIsometries.hJ_smul_left, hx, mul_zero]

theorem spanLt_le (a : ℕ) (h : a ≤ r) : spanLt e a ≤ spanLt e r := by
  unfold spanLt
  refine Submodule.span_mono ?_
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨b, b.2, rfl⟩

theorem mem_NH {w : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k) {s : UJ ε}
    (hs : s ∈ UnitaryIsometries.RI.SG ε e z) : ∃ m ∈ NG ε e z, ∃ h ∈ HG ε e p z, s = m * h := by
  set M := Formalism.MainNotions.S.uMat s with hM
  have hsi : s⁻¹ ∈ UnitaryIsometries.RI.SG ε e z := (UnitaryIsometries.RI.SG ε e z).inv_mem hs
  have hiso := UnitaryIsometries.isIsom_uMat ε s
  have hback : ∀ v : Fin n → ℂ, M *ᵥ (Formalism.MainNotions.S.uMat s⁻¹ *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, hM, uMat_mul_inv, one_mulVec]
  have hMe : ∀ a j, hJ ε (e a) (M *ᵥ w j) = 0 := by
    intro a j
    rw [← hback (e a), hiso]
    have hx := hsi.1 a
    have hdec : Formalism.MainNotions.S.uMat s⁻¹ *ᵥ e a = e a + (Formalism.MainNotions.S.uMat s⁻¹ - 1) *ᵥ e a := by
      rw [Matrix.sub_mulVec, one_mulVec]; abel
    rw [hdec, UnitaryIsometries.hJ_add_left, Fw.ew, span_perp Fw a.1 _ hx j, add_zero]
  have hMz : ∀ j, hJ ε z (M *ᵥ w j) = 0 := by
    intro j
    rw [← hback z, hiso]
    have hx := hsi.2
    have hdec : Formalism.MainNotions.S.uMat s⁻¹ *ᵥ z = z + (Formalism.MainNotions.S.uMat s⁻¹ - 1) *ᵥ z := by
      rw [Matrix.sub_mulVec, one_mulVec]; abel
    rw [hdec, UnitaryIsometries.hJ_add_left, Fw.zw, span_perp Fw r _ hx j, add_zero]
  set y : Fin k → Fin n → ℂ := fun j => M *ᵥ w j - ∑ a, hJ ε (p a) (M *ᵥ w j) • e a with hy
  have hpe : ∀ a b, hJ ε (p a) (e b) = if b = a then 1 else 0 := fun a b => hJ_swapδ Fw.ep b a
  have hwe : ∀ j b, hJ ε (M *ᵥ w j) (e b) = 0 := fun j b => hJ_swap0 (hMe b j)
  have Fy : Frm ε e p z y T := by
    refine ⟨Fw.ee, Fw.ep, Fw.pp, Fw.ez, Fw.pz, Fw.zz, fun a j => ?_, fun a j => ?_, fun j => ?_, fun i j => ?_,
      Fw.T_ne⟩
    · simp only [hy, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sum_right, Fw.ee, mul_zero, Finset.sum_const_zero, sub_zero, hMe]
    · simp only [hy, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sum_right, hpe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    · have hze : ∀ b, hJ ε z (e b) = 0 := fun b => hJ_swap0 (Fw.ez b)
      simp only [hy, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sum_right, hze, mul_zero, Finset.sum_const_zero, sub_zero, hMz]
    · simp only [hy, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_sum_right, UnitaryIsometries.hJ_sum_left, hwe, Fw.ee, hMe,
        mul_zero, Finset.sum_const_zero, sub_zero]
      rw [hM]
      exact (hiso _ _).trans (Fw.ww i j)
  have hI := frM_isIsom Fw Fy hdim
  set hU := UnitaryIsometries.toUJ ε hI with hUdef
  have hUm : Formalism.MainNotions.S.uMat hU = frM (ε := ε) e p z w y T := UnitaryIsometries.uMat_toUJ ε hI
  have hUe : ∀ a, Formalism.MainNotions.S.uMat hU *ᵥ e a = e a := fun a => by
    rw [hUm]; exact frM_fix Fw hdim fun j => hJ_swap0 (Fw.ew a j)
  have hUp : ∀ a, Formalism.MainNotions.S.uMat hU *ᵥ p a = p a := fun a => by
    rw [hUm]; exact frM_fix Fw hdim fun j => hJ_swap0 (Fw.pw a j)
  have hUz : Formalism.MainNotions.S.uMat hU *ᵥ z = z := by
    rw [hUm]; exact frM_fix Fw hdim fun j => hJ_swap0 (Fw.zw j)
  have hUH : hU ∈ HG ε e p z := ⟨hUe, hUp, hUz⟩
  have hUw : ∀ j, Formalism.MainNotions.S.uMat hU⁻¹ *ᵥ y j = w j := fun j => by
    rw [← frM_w (y := y) Fw j, ← hUm, mulVec_mulVec, uMat_inv_mul, one_mulVec]
  refine ⟨s * hU⁻¹, ?_, hU, hUH, by group⟩
  have hmv : ∀ v, (Formalism.MainNotions.S.uMat (s * hU⁻¹) - 1) *ᵥ v = M *ᵥ (Formalism.MainNotions.S.uMat hU⁻¹ *ᵥ v) - v := fun v => by
    rw [uMat_mul, Matrix.sub_mulVec, one_mulVec, ← mulVec_mulVec]
  have hme : ∀ a, (Formalism.MainNotions.S.uMat (s * hU⁻¹) - 1) *ᵥ e a = (M - 1) *ᵥ e a := fun a => by
    rw [hmv, inv_fix ε (hUe a), Matrix.sub_mulVec, one_mulVec]
  have hmz : (Formalism.MainNotions.S.uMat (s * hU⁻¹) - 1) *ᵥ z = (M - 1) *ᵥ z := by
    rw [hmv, inv_fix ε hUz, Matrix.sub_mulVec, one_mulVec]
  have hmy : ∀ j, (Formalism.MainNotions.S.uMat (s * hU⁻¹) - 1) *ᵥ y j ∈ spanLt e r := fun j => by
    rw [hmv, hUw, hy, sub_sub_cancel]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, a.2, rfl⟩)
  refine ⟨⟨fun a => ?_, ?_⟩, fun v hv => ?_⟩
  · rw [hme]; exact hs.1 a
  · rw [hmz]; exact hs.2
  · rw [recon Fy hdim v]
    simp only [syn, mulVec_add, mulVec_sum, mulVec_smul, hv, zero_smul, Finset.sum_const_zero, add_zero]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ ?_)) (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmy j))
    · rw [hme]; exact spanLt_le a.1 (le_of_lt a.2) (hs.1 a)
    · rw [hmz]; exact hs.2

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
