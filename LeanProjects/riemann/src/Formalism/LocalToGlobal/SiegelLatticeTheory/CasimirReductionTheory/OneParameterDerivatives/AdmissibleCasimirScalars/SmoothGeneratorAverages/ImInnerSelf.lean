import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CompactDerivativesBounded
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted.BoundedOperators

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def aop (D : Submodule ℂ H) (T : H → H) (hadd : ∀ u ∈ D, ∀ v ∈ D, T (u + v) = T u + T v)
    (hsm : ∀ (c : ℂ), ∀ v ∈ D, T (c • v) = c • T v) : D →ₗ[ℂ] H where
  toFun u := T u + Complex.I • (u : H)
  map_add' u v := by
    simp only [Submodule.coe_add, hadd u u.2 v v.2, smul_add]
    abel
  map_smul' c u := by
    simp only [Submodule.coe_smul, hsm c u u.2, RingHom.id_apply, smul_add, smul_comm c Complex.I]

theorem aop_apply (D : Submodule ℂ H) (T : H → H) (hadd : ∀ u ∈ D, ∀ v ∈ D, T (u + v) = T u + T v)
    (hsm : ∀ (c : ℂ), ∀ v ∈ D, T (c • v) = c • T v) (u : D) :
    aop D T hadd hsm u = T u + Complex.I • (u : H) := rfl

theorem im_inner_self (T : H → H) (u : H) (h : ⟪T u, u⟫_ℂ = ⟪u, T u⟫_ℂ) : (⟪T u, u⟫_ℂ).im = 0 := by
  rw [← Complex.conj_eq_iff_im, inner_conj_symm]
  exact h.symm

theorem norm_le_aop (T : H → H) (u : H) (h : ⟪T u, u⟫_ℂ = ⟪u, T u⟫_ℂ) : ‖u‖ ≤ ‖T u + Complex.I • u‖ := by
  have h1 : ‖T u + Complex.I • u‖ ^ 2 = ‖T u‖ ^ 2 + ‖u‖ ^ 2 := by
    rw [@norm_add_sq ℂ, inner_smul_right, norm_smul, Complex.norm_I, one_mul]
    have h2 : RCLike.re (Complex.I * ⟪T u, u⟫_ℂ) = 0 := by
      show (Complex.I * ⟪T u, u⟫_ℂ).re = 0
      rw [Complex.mul_re, Complex.I_re, Complex.I_im, im_inner_self T u h]
      ring
    rw [h2]
    ring
  have h3 : ‖u‖ ^ 2 ≤ ‖T u + Complex.I • u‖ ^ 2 := by
    rw [h1]
    nlinarith [sq_nonneg ‖T u‖]
  nlinarith [norm_nonneg u, norm_nonneg (T u + Complex.I • u)]

end Formalism.L2.SG.Pf.admitted.BoundedOperators

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX Formalism.L2.SG.Pf.admitted.BoundedOperators

theorem c3 : SchurSymmetricDense := by
  intro n ε H _ _ _ σ hU hI D _hD hst T hadd hsm hsym hcomm
  by_cases h0 : ∀ v ∈ D, v = 0
  · refine ⟨0, fun v hv => ?_⟩
    rw [h0 v hv]
    have := hsm 0 0 D.zero_mem
    simpa using this
  push Not at h0
  obtain ⟨u0, hu0D, hu0⟩ := h0
  let A := aop D T hadd hsm
  have hbd : ∀ u : D, ‖D.subtype u‖ ≤ 1 * ‖A u‖ := by
    intro u
    rw [one_mul]
    exact norm_le_aop T u (hsym u u.2 u u.2)

  have hAg : ∀ (g : UJ ε) (u : D), σ (umat g) (A u) = A ⟨σ (umat g) u, hst g u u.2⟩ := by
    intro g u
    rw [aop_apply, aop_apply, map_add, map_smul, hcomm g u u.2]

  set S := (LinearMap.range A)ᗮ with hS
  have hSst : ∀ (g : UJ ε), ∀ x ∈ S, σ (umat g) x ∈ S := by
    intro g x hx
    rw [Submodule.mem_orthogonal]
    rintro y ⟨u, rfl⟩
    rw [← inv_inv g, ← rep_inner_left hU g⁻¹, hAg]
    exact (Submodule.mem_orthogonal _ _).1 hx _ ⟨_, rfl⟩
  have hdense : DenseRange A := by
    rcases Formalism.MainNotions.BridgeCSchur.irr_of hI S (Submodule.isClosed_orthogonal _) hSst with h | h
    · have h2 : (LinearMap.range A).topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.2 h
      have h3 := (Submodule.dense_iff_topologicalClosure_eq_top).2 h2
      exact h3
    · exfalso
      have hm : A ⟨u0, hu0D⟩ ∈ S := by rw [h]; trivial
      have hz : ⟪A ⟨u0, hu0D⟩, A ⟨u0, hu0D⟩⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 hm _ ⟨_, rfl⟩
      rw [inner_self_eq_zero] at hz
      have := hbd ⟨u0, hu0D⟩
      rw [hz, norm_zero, mul_zero] at this
      exact hu0 (norm_le_zero_iff.1 this)
  let R : H →L[ℂ] H := LinearMap.extendOfNorm D.subtype A
  have hR : ∀ u : D, R (A u) = u := fun u => LinearMap.extendOfNorm_eq hdense ⟨1, hbd⟩ u
  have hRg : ∀ (g : UJ ε), R.comp (σ (umat g)) = (σ (umat g)).comp R := by
    intro g
    ext x
    refine hdense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro u
    simp only [ContinuousLinearMap.comp_apply]
    rw [hAg, hR, hR]
  let U : Set (H →L[ℂ] H) := Set.range (fun g : UJ ε => σ (umat g))
  have hstar : ∀ V ∈ U, star V ∈ U := by
    rintro V ⟨g, rfl⟩
    refine ⟨g⁻¹, ?_⟩
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [rep_inner_left hU, inv_inv]
  have hirr : ∀ S' : Submodule ℂ H, IsClosed (S' : Set H) → (∀ V ∈ U, ∀ v ∈ S', V v ∈ S') → S' = ⊥ ∨ S' = ⊤ :=
    fun S' hS' h => Formalism.MainNotions.BridgeCSchur.irr_of hI S' hS' (fun g v hv => h _ ⟨g, rfl⟩ v hv)
  have hcommR : ∀ V ∈ U, Commute R V := by
    rintro V ⟨g, rfl⟩
    exact hRg g
  obtain ⟨lam, hlam⟩ := Formalism.MainNotions.BridgeCSchur.schur_bounded U hstar hirr R hcommR
  have hkey : ∀ u : D, (u : H) = lam • (T u + Complex.I • (u : H)) := by
    intro u
    have h1 := hR u
    rw [hlam, _root_.smul_apply, one_apply_eq_self] at h1
    exact h1.symm
  have hlam0 : lam ≠ 0 := by
    intro hl
    have := hkey ⟨u0, hu0D⟩
    rw [hl, zero_smul] at this
    exact hu0 this
  set mu : ℂ := lam⁻¹ - Complex.I with hmu
  have hT : ∀ v ∈ D, T v = mu • v := by
    intro v hv
    have h1 : v = lam • (T v + Complex.I • v) := hkey ⟨v, hv⟩
    have h2 : lam⁻¹ • v = T v + Complex.I • v := by
      calc lam⁻¹ • v = lam⁻¹ • (lam • (T v + Complex.I • v)) := congrArg _ h1
        _ = T v + Complex.I • v := by rw [smul_smul, inv_mul_cancel₀ hlam0, one_smul]
    rw [hmu, sub_smul, h2]
    abel
  have hreal : mu.im = 0 := by
    have h1 := hsym u0 hu0D u0 hu0D
    rw [hT u0 hu0D, inner_smul_left, inner_smul_right] at h1
    have hne : ⟪u0, u0⟫_ℂ ≠ 0 := by rwa [ne_eq, inner_self_eq_zero]
    have h2 := mul_right_cancel₀ hne h1
    exact Complex.conj_eq_iff_im.1 h2
  refine ⟨mu.re, fun v hv => ?_⟩
  rw [hT v hv]
  congr 1
  exact Complex.ext (by simp) (by simp [hreal])

end Formalism.L2.SG.Pf.admitted
