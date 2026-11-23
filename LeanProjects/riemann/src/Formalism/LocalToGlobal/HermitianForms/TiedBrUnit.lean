import Formalism.LocalToGlobal.HermitianForms.TiedBr

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions Matrix

theorem isUnit_det_cols {E : Type} [Field E] {N n : ℕ} (hN : n + 1 = N) (A : Matrix (Fin N) (Fin n) E) (z : Fin N → E)
    (hA : Function.Injective A.mulVec) (hz : ∀ x, A *ᵥ x ≠ z) :
    IsUnit (Matrix.of (fun a (b : Fin N) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a)).det := by
  subst hN
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v1 v2 h12
  have hv : (Matrix.of fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) *ᵥ (v1 - v2) = 0 := by
    rw [Matrix.mulVec_sub, h12, sub_self]
  rw [← sub_eq_zero]
  generalize v1 - v2 = v at hv ⊢
  have hsplit : ∀ a, ((Matrix.of fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) *ᵥ v) a =
      (A *ᵥ fun j => v j.castSucc) a + v (Fin.last n) * z a := by
    intro a
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, mul_comm]
  have hv' : ∀ a, (A *ᵥ fun j => v j.castSucc) a + v (Fin.last n) * z a = 0 := fun a => by
    rw [← hsplit]; exact congrFun hv a
  have hlast : v (Fin.last n) = 0 := by
    by_contra h
    apply hz (-(v (Fin.last n))⁻¹ • fun j : Fin n => v j.castSucc)
    funext a
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    have e : (A *ᵥ fun j : Fin n => v j.castSucc) a = -(v (Fin.last n) * z a) := by linear_combination hv' a
    rw [e]; field_simp
  have hcs : (fun j : Fin n => v j.castSucc) = 0 := by
    apply hA
    funext a
    have := hv' a
    rw [hlast, zero_mul, add_zero] at this
    rw [this, Matrix.mulVec_zero]; rfl
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · exact hlast
  · exact congrFun hcs i

variable (D : D7)

theorem iX'_injective : letI := D.host.cmStar; Function.Injective D.sp.iX' := by
  letI := D.host.cmStar
  intro x y h
  rw [← sub_eq_zero]
  have h0 : D.sp.iX' (x - y) = 0 := by rw [map_sub, h, sub_self]
  apply D.sp.X'.nondeg.1 (x - y)
  intro w
  rw [← D.sp.iX'_isom (x - y) w, h0, map_zero, LinearMap.zero_apply]

theorem iXc_injective : Function.Injective (iXc D) := by
  letI := D.host.cmStar
  intro x y h
  unfold iXc at h
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, EmbeddingLike.apply_eq_iff_eq] at h
  exact (LinearEquiv.injective _) (iX'_injective D h)

theorem iXm_mulVec_injective : Function.Injective (iXm D).mulVec := by
  intro x y h
  simp only [iXm, LinearMap.toMatrix'_mulVec] at h
  exact iXc_injective D h

variable {D}

theorem vector_quotient_not_in_range {u : D.what₂.Word} (Tf : FormsTied D u) (x : Fin (D.R.N D.R.m - 1) → D.host.E) :
    iXm D *ᵥ x ≠ fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E) := by
  letI := D.host.cmStar
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    rw [ha, zero_smul] at h
    simp [Formalism.UG.hform] at h
    exact hT h.symm
  intro hx
  simp only [iXm, LinearMap.toMatrix'_mulVec] at hx
  have hc : iXc D x = (a / ((D.mem u).A.T : D.host.E)) • zc D := by
    rw [hx]; funext i; rw [ha]; simp [Pi.smul_apply, smul_eq_mul]; ring
  unfold iXc zc at hc
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, ← map_smul,
    EmbeddingLike.apply_eq_iff_eq] at hc
  have h1 := D.sp.z_orth ((D.sp.X'.frame.equivFun.trans
      (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)).symm x)
  rw [hc, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact div_ne_zero ha0 hT ((map_eq_zero _).mp h2)
  · exact D.sp.z_anis h2

theorem bZ_isUnit {u : D.what₂.Word} (Tf : FormsTied D u) : IsUnit (bZ u Tf.til.z0).det :=
  isUnit_det_cols (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (iXm D) (fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E))
    (iXm_mulVec_injective D) (vector_quotient_not_in_range Tf)

end Formalism.L2.Forms
