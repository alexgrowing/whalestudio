import Formalism.LocalToGlobal.GlobalTheory.BlockActions.MulLatMulLat
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.HformSmulRightB
import Formalism.LocalToGlobal.GlobalTheory.ExistsUnitaryOneDetEq

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

theorem span_of_cols {E : Type} [Field E] {N n : ℕ} (hN : n + 1 = N) (A : Matrix (Fin N) (Fin n) E) (z : Fin N → E)
    (hA : Function.Injective A.mulVec) (hz : ∀ x, A *ᵥ x ≠ z) :
    ∀ y, ∃ (x : Fin n → E) (s : E), y = A *ᵥ x + s • z := by
  subst hN
  intro y
  have hB := isUnit_det_cols rfl A z hA hz
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
    Matrix.of (fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) with hBdef
  set w := B⁻¹ *ᵥ y with hw
  have hy : B *ᵥ w = y := by rw [hw, mulVec_mulVec, mul_nonsing_inv _ hB, one_mulVec]
  refine ⟨fun i => w (Fin.castSucc i), w (Fin.last n), ?_⟩
  rw [← hy]
  funext a
  simp only [hBdef, mulVec, dotProduct, Fin.sum_univ_castSucc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, of_apply,
    Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true, Fin.eta]
  ring

variable (D : D7)

theorem conj_sigD (φ : D.host.E →+* ℂ) (x : D.host.E) :
    φ ((sigD D : D.host.E →+* D.host.E) x) = (starRingEnd ℂ) (φ x) := by
  letI := D.host.cmStar
  exact D.sp.cm.cmUnram.2.1 φ x

theorem zc_not_range (x : Fin (D.R.N D.R.m - 1) → D.host.E) : iXm D *ᵥ x ≠ zc D := by
  letI := D.host.cmStar
  intro h
  have h1 := hform_iXc_zc D x
  simp only [iXm, LinearMap.toMatrix'_mulVec] at h
  rw [h, zc_eq, hform_crdM] at h1
  exact D.sp.z_anis h1

theorem span_iXc_zc : ∀ y, ∃ (x : Fin (D.R.N D.R.m - 1) → D.host.E) (s : D.host.E), y = iXc D x + s • zc D := by
  intro y
  obtain ⟨x, s, h⟩ := span_of_cols (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (iXm D) (zc D) (iXm_mulVec_injective D) (zc_not_range D) y
  refine ⟨x, s, ?_⟩
  rw [h]
  simp only [iXm, LinearMap.toMatrix'_mulVec]

variable {D}

theorem defN_of_fact {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (C : GL (Fin n) D.host.E)
    (hC : cT (sigD D : D.host.E →+* D.host.E) C.1 * C.1 = J) (φ : D.host.E →+* ℂ) (x : Fin n → D.host.E) :
    ∃ r : ℝ, 0 ≤ r ∧ φ (hform (sigD D : D.host.E →+* D.host.E) J x x) = r ∧ (r = 0 → x = 0) := by
  have e1 : hform (sigD D : D.host.E →+* D.host.E) J x x =
      ∑ a, (sigD D : D.host.E →+* D.host.E) ((C.1 *ᵥ x) a) * (C.1 *ᵥ x) a := by
    rw [← hC, ← Matrix.mul_one (cT (sigD D : D.host.E →+* D.host.E) C.1), ← Formalism.L2.GlobalTheoryTheory.Comp.hform_mulVec_rect]
    simp only [hform, one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨∑ a, Complex.normSq (φ ((C.1 *ᵥ x) a)), Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _), ?_, ?_⟩
  · rw [e1, map_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_mul, conj_sigD, Complex.normSq_eq_conj_mul_self]
  · intro h0
    have hz : C.1 *ᵥ x = 0 := by
      funext a
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)).mp h0 a (Finset.mem_univ _)
      rw [Complex.normSq_eq_zero, map_eq_zero] at this
      exact this
    have hCi : IsUnit C.1.det := (Matrix.isUnit_iff_isUnit_det _).mp C.isUnit
    calc x = C.1⁻¹ *ᵥ (C.1 *ᵥ x) := by rw [mulVec_mulVec, nonsing_inv_mul _ hCi, one_mulVec]
      _ = 0 := by rw [hz, mulVec_zero]

variable {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem crdFacts_of (Tf : FormsTiedSym D u Ch chOf) : CrdFacts D := by
  obtain ⟨C, hC, -, -⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).de
  exact
    { conj := conj_sigD D
      defN := fun φ x => defN_of_fact (gramN D D.R.m le_rfl) C hC φ x
      iso := hform_iXc D
      orth := fun x => ⟨hform_iXc_zc D x, hform_zc_iXc D x⟩
      span := span_iXc_zc D }

end Formalism.L2.GlobalTheoryTheory.Br
