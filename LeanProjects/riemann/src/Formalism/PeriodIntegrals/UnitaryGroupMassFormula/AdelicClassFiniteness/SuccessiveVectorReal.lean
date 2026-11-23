import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartShortOf

noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField Matrix
open scoped ComplexOrder

section Gen

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem svR_form {o : Type*} [Fintype o] (X : Matrix o κ ℂ) (A : Matrix o o ℂ) (v : κ → ℂ) :
    star (X *ᵥ v) ⬝ᵥ (A *ᵥ (X *ᵥ v)) = star v ⬝ᵥ ((Xᴴ * A * X) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem svR_det (eq : κ ≃ ι) (X : Matrix ι κ ℂ) (B : Matrix ι ι ℂ) :
    (Xᴴ * B * X).det = star (X.submatrix eq id).det * B.det * (X.submatrix eq id).det := by
  have hY : Xᴴ * B * X = (X.submatrix eq id)ᴴ * B.submatrix eq eq * X.submatrix eq id := by
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id]
  rw [hY, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_submatrix_equiv_self]

theorem svR_entry {o : Type*} [Fintype o] (X : Matrix o κ ℂ) (A : Matrix o o ℂ) (i j : κ) :
    (Xᴴ * A * X) i j = ∑ k, ∑ l, star (X k i) * A k l * X l j := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

end Gen

section Coord

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def svP {m N : ℕ} (e : Fin N → Fin m → E) (φ : E →+* ℂ) : Matrix (Fin m) (Fin N) ℂ :=
  Matrix.of fun k i => φ (e i k)

def svBig {m N : ℕ} (e : Fin N → Fin m → E) : Matrix (Fin m × (E →+* ℂ)) (Fin N) ℂ :=
  Matrix.of fun p i => p.2 (e i p.1)

theorem svBig_block [DecidableEq (E →+* ℂ)] {m N : ℕ} (e : Fin N → Fin m → E)
    (A : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ) :
    (svBig e)ᴴ * blockDiagonal A * svBig e = ∑ φ, (svP e φ)ᴴ * A φ * svP e φ := by
  ext i j
  rw [svR_entry, Matrix.sum_apply]
  simp_rw [svR_entry]
  simp only [svBig, svP, Matrix.of_apply, Matrix.blockDiagonal_apply, Fintype.sum_prod_type,
    mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]

theorem svR_hform (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {m : ℕ}
    (J : Matrix (Fin m) (Fin m) E) (φ : E →+* ℂ) (x y : Fin m → E) :
    φ (hform (starRingEnd E) J x y) = ∑ k, ∑ l, star (φ (x k)) * φ (J k l) * φ (y l) := by
  simp only [hform, map_sum, map_mul, starRingEnd_apply]
  simp only [hst, starRingEnd_apply]

theorem svR_hdot (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {m : ℕ}
    (J : Matrix (Fin m) (Fin m) E) (φ : E →+* ℂ) (x y : Fin m → E) :
    φ (hform (starRingEnd E) J x y) =
      star (fun k => φ (x k)) ⬝ᵥ (J.map φ *ᵥ fun l => φ (y l)) := by
  rw [svR_hform hst]
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum, mul_assoc]

theorem svR_trace (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {m N : ℕ}
    (J : Matrix (Fin m) (Fin m) E) (e : Fin N → Fin m → E) :
    (gramTr J e).map (Rat.castHom ℂ) = ∑ φ, (svP e φ)ᴴ * J.map φ * svP e φ := by
  ext i j
  rw [Matrix.map_apply, Matrix.sum_apply]
  simp_rw [svR_entry]
  simp only [gramTr, svP, Matrix.of_apply, Matrix.map_apply]
  have hcast : ∀ q : ℚ, (Rat.castHom ℂ) q = algebraMap ℚ ℂ q := fun q => by simp
  rw [hcast, trace_eq_sum_embeddings ℂ, ← Equiv.sum_comp (RingHom.equivRatAlgHom E ℂ)]
  refine Finset.sum_congr rfl (fun φ _ => ?_)
  exact svR_hform hst J φ (e i) (e j)

theorem svR_conj {m N : ℕ} (e : Fin N → Fin m → E) (H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ)
    (φ : E →+* ℂ) (hc : H (ComplexEmbedding.conjugate φ) = (H φ).map (starRingEnd ℂ)) :
    (svP e (ComplexEmbedding.conjugate φ))ᴴ * H (ComplexEmbedding.conjugate φ) *
        svP e (ComplexEmbedding.conjugate φ) = ((svP e φ)ᴴ * H φ * svP e φ).map (starRingEnd ℂ) := by
  ext i j
  rw [hc, Matrix.map_apply, svR_entry, svR_entry]
  simp only [svP, Matrix.of_apply, Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq, map_sum,
    map_mul, starRingEnd_apply, star_star]

theorem svR_normsq (z X : ℂ) : star z * X * z = ((‖z‖ ^ 2 : ℝ) : ℂ) * X := by
  have h : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  calc star z * X * z = (z * star z) * X := by ring
    _ = _ := by rw [h]

end Coord

theorem successive_vector_real : SvReal := by
  intro F E _ _ _ _ _ _ hcm m J hJ H hH e hdet
  classical
  have hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a) := hcm.cmUnram.2.1

  set M : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℂ :=
    ∑ φ, (svP e φ)ᴴ * H φ * svP e φ with hM

  have hMc : ∀ i j, starRingEnd ℂ (M i j) = M i j := by
    intro i j
    simp only [hM, Matrix.sum_apply, map_sum]
    have hT : ∀ φ : E →+* ℂ, starRingEnd ℂ (((svP e φ)ᴴ * H φ * svP e φ) i j) =
        ((svP e (ComplexEmbedding.conjugate φ))ᴴ * H (ComplexEmbedding.conjugate φ) *
          svP e (ComplexEmbedding.conjugate φ)) i j := by
      intro φ
      rw [svR_conj e H φ (hH φ).2.2.2, Matrix.map_apply]
    simp_rw [hT]
    exact Equiv.sum_comp ((ComplexEmbedding.involutive_conjugate E).toPerm _)
      (fun φ => ((svP e φ)ᴴ * H φ * svP e φ) i j)

  have hHh : ∀ φ, (H φ)ᴴ = H φ := fun φ => (hH φ).1.1
  have hMH : Mᴴ = M := by
    simp only [hM, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hHh, Matrix.mul_assoc]
  set R : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℝ :=
    M.map Complex.re with hR
  have hMR : R.map (fun x : ℝ => (x : ℂ)) = M := by
    ext i j
    simp only [hR, Matrix.map_apply]
    exact Complex.conj_eq_iff_re.1 (hMc i j)

  have hsum : ∀ u, star u ⬝ᵥ (M *ᵥ u) =
      ∑ φ : E →+* ℂ, star (svP e φ *ᵥ u) ⬝ᵥ (H φ *ᵥ (svP e φ *ᵥ u)) := by
    intro u
    rw [hM, Matrix.sum_mulVec, dotProduct_sum]
    simp_rw [svR_form]
  have hq : ∀ v : Fin (m * Module.finrank ℚ E) → ℝ, v ⬝ᵥ (R *ᵥ v) =
      (star (fun i => (v i : ℂ)) ⬝ᵥ (M *ᵥ fun i => (v i : ℂ))).re := by
    intro v
    rw [← hMR]
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Complex.star_def,
      Complex.conj_ofReal, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.im_sum, zero_mul, sub_zero, mul_zero]
  have hnn : ∀ u, 0 ≤ (star u ⬝ᵥ (M *ᵥ u)).re := by
    intro u
    rw [hsum, Complex.re_sum]
    exact Finset.sum_nonneg (fun φ _ => (norm_nonneg _).trans ((hH φ).2.2.1 _))

  have hcard : Fintype.card (Fin (m * Module.finrank ℚ E)) = Fintype.card (Fin m × (E →+* ℂ)) := by
    simp [Fintype.card_prod, NumberField.Embeddings.card]
  set eqv : Fin (m * Module.finrank ℚ E) ≃ Fin m × (E →+* ℂ) := Fintype.equivOfCardEq hcard
  set d := ((svBig e).submatrix eqv id).det with hd
  have hdG : ((gramTr J e).det : ℂ) = star d * (∏ φ : E →+* ℂ, (J.map φ).det) * d := by
    have h1 := congrArg Matrix.det (svR_trace hst J e)
    rw [← svBig_block e (fun φ => J.map φ), svR_det eqv, Matrix.det_blockDiagonal] at h1
    rw [← h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simp
  have hdM : M.det = star d * (∏ φ : E →+* ℂ, (H φ).det) * d := by
    rw [hM, ← svBig_block e H, svR_det eqv, Matrix.det_blockDiagonal]
  have hRdet : R.det = |((gramTr J e).det : ℝ)| := by
    have h1 : ((R.det : ℝ) : ℂ) = M.det := by
      rw [← hMR]
      exact RingHom.map_det Complex.ofRealHom R
    have h2 : M.det = ((‖((gramTr J e).det : ℂ)‖ : ℝ) : ℂ) := by
      rw [hdM, hdG]
      simp only [(fun φ => (hH φ).2.1 : ∀ φ, (H φ).det = ((‖(J.map φ).det‖ : ℝ) : ℂ))]
      rw [norm_mul, norm_mul, norm_star, norm_prod]
      push_cast
      have hs : star d * d = ((‖d‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc star d * (∏ φ : E →+* ℂ, ((‖(J.map φ).det‖ : ℝ) : ℂ)) * d
          = (star d * d) * (∏ φ : E →+* ℂ, ((‖(J.map φ).det‖ : ℝ) : ℂ)) := by ring
        _ = _ := by rw [hs]; push_cast; ring
    have h3 := h1.trans h2
    rw [Complex.ofReal_inj] at h3
    rw [h3, Complex.norm_ratCast]
  refine ⟨R, ?_, hRdet, ?_⟩
  ·
    have hRh : R.IsHermitian := by
      ext i j
      simp only [hR, Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial]
      have := congrFun (congrFun hMH i) j
      rw [Matrix.conjTranspose_apply] at this
      rw [← this, Complex.star_def, Complex.conj_re]
    have hPSD : R.PosSemidef := by
      refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨hRh, fun v => ?_⟩
      rw [star_trivial, hq v]
      exact hnn _
    refine (hPSD.posDef_iff_isUnit).2 ((Matrix.isUnit_iff_isUnit_det R).2 (isUnit_iff_ne_zero.2 ?_))
    rw [hRdet]
    exact abs_ne_zero.2 (Rat.cast_ne_zero.2 hdet)
  · intro c
    have hx : ∀ φ : E →+* ℂ, (fun k => φ ((∑ i, (c i : E) • e i) k)) =
        svP e φ *ᵥ fun i => ((c i : ℝ) : ℂ) := by
      intro φ
      ext k
      simp only [svP, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, map_sum, map_mul, map_intCast]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      push_cast
      ring
    calc ∑ φ : E →+* ℂ, ‖φ (hform (starRingEnd E) J (∑ i, (c i : E) • e i) (∑ i, (c i : E) • e i))‖
        ≤ ∑ φ : E →+* ℂ, (star (svP e φ *ᵥ fun i => ((c i : ℝ) : ℂ)) ⬝ᵥ
            (H φ *ᵥ (svP e φ *ᵥ fun i => ((c i : ℝ) : ℂ)))).re := by
          refine Finset.sum_le_sum (fun φ _ => ?_)
          rw [svR_hdot hst, hx φ]
          exact (hH φ).2.2.1 _
      _ = (star (fun i => ((c i : ℝ) : ℂ)) ⬝ᵥ (M *ᵥ fun i => ((c i : ℝ) : ℂ))).re := by
          rw [hsum, Complex.re_sum]
      _ = (fun i => (c i : ℝ)) ⬝ᵥ (R *ᵥ fun i => (c i : ℝ)) := (hq _).symm

end PIW.AdelClassFin
