import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef

set_option autoImplicit false

noncomputable section

open Matrix GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CurvInterp

section Linear

variable {n : Type} [Fintype n] [DecidableEq n]

theorem form_dualGram_star {M : Matrix n n ℂ} (hM : IsUnit M.det) (u y : n → ℂ) :
    form (dualGram M) u (star (Mᵀ *ᵥ y)) = u ⬝ᵥ y := by
  rw [form, star_star, dualGram, mulVec_mulVec, ← transpose_mul, mul_nonsing_inv _ hM,
    transpose_one, one_mulVec]

theorem star_mulVec_dualGram {M : Matrix n n ℂ} (hM : IsUnit M.det) (u : n → ℂ) :
    star (Mᵀ *ᵥ (dualGram M *ᵥ star u)) = u := by
  rw [dualGram, mulVec_mulVec, ← transpose_mul, nonsing_inv_mul _ hM, transpose_one, one_mulVec,
    star_star]

theorem form_dualGram_star_self {M : Matrix n n ℂ} (hH : M.IsHermitian) (hM : IsUnit M.det)
    (y : n → ℂ) : form (dualGram M) (star (Mᵀ *ᵥ y)) (star (Mᵀ *ᵥ y)) = form M y y := by
  rw [form_dualGram_star hM, form_eq_transpose, star_mulVec, ← dotProduct_mulVec,
    hH.transpose.eq]

theorem gnorm_dualGram_star {M : Matrix n n ℂ} (hH : M.IsHermitian) (hM : IsUnit M.det)
    (y : n → ℂ) : gnorm (dualGram M) (star (Mᵀ *ᵥ y)) = gnorm M y := by
  rw [gnorm, gnorm, form_dualGram_star_self hH hM]

theorem posDef_dualGram {M : Matrix n n ℂ} (hM : M.PosDef) : (dualGram M).PosDef :=
  hM.inv.transpose

theorem le_of_sq_le_mul {N a : ℝ} (hN : 0 ≤ N) (ha : 0 ≤ a) (h : N ^ 2 ≤ a * N) : N ≤ a := by
  rcases hN.eq_or_lt with h0 | h0
  · rw [← h0]; exact ha
  · exact le_of_mul_le_mul_right (by nlinarith) h0

theorem opNorm_dualGram_transpose_le {M : Matrix n n ℂ} (hM : M.PosDef) (T : Matrix n n ℂ) :
    opNorm (dualGram M) (dualGram M) Tᵀ ≤ opNorm M M T := by
  have hu : IsUnit M.det := (isUnit_iff_isUnit_det _).1 hM.isUnit
  have hK := posDef_dualGram hM
  refine opNorm_le_of_bound (opNorm_nonneg _ _ _) fun u => ?_
  have hx : star (Mᵀ *ᵥ (dualGram M *ᵥ star (Tᵀ *ᵥ u))) = Tᵀ *ᵥ u := star_mulVec_dualGram hu _
  set x := Tᵀ *ᵥ u with hxdef
  set w := dualGram M *ᵥ star x
  have e : form (dualGram M) x x = form (dualGram M) u (star (Mᵀ *ᵥ (T *ᵥ w))) := by
    calc form (dualGram M) x x = form (dualGram M) x (star (Mᵀ *ᵥ w)) := by rw [hx]
      _ = x ⬝ᵥ w := form_dualGram_star hu x w
      _ = u ⬝ᵥ T *ᵥ w := by
          show (Tᵀ *ᵥ u) ⬝ᵥ w = u ⬝ᵥ T *ᵥ w
          rw [mulVec_transpose, ← dotProduct_mulVec]
      _ = _ := (form_dualGram_star hu u _).symm
  have hw : gnorm M w = gnorm (dualGram M) x := by rw [← gnorm_dualGram_star hM.isHermitian hu, hx]
  have h1 : gnorm (dualGram M) x ^ 2 ≤ gnorm (dualGram M) u * opNorm M M T * gnorm (dualGram M) x := by
    calc gnorm (dualGram M) x ^ 2 = (form (dualGram M) x x).re := gnorm_sq hK.posSemidef x
      _ ≤ ‖form (dualGram M) x x‖ := Complex.re_le_norm _
      _ = ‖form (dualGram M) u (star (Mᵀ *ᵥ (T *ᵥ w)))‖ := by rw [e]
      _ ≤ gnorm (dualGram M) u * gnorm (dualGram M) (star (Mᵀ *ᵥ (T *ᵥ w))) :=
          norm_form_le hK.posSemidef _ _
      _ = gnorm (dualGram M) u * gnorm M (T *ᵥ w) := by
          rw [gnorm_dualGram_star hM.isHermitian hu]
      _ ≤ gnorm (dualGram M) u * (opNorm M M T * gnorm M w) :=
          mul_le_mul_of_nonneg_left (gnorm_mulVec_le hM hM.posSemidef T w) (gnorm_nonneg _ _)
      _ = _ := by rw [hw]; ring
  rw [mul_comm]
  exact le_of_sq_le_mul (gnorm_nonneg _ _)
    (mul_nonneg (gnorm_nonneg _ _) (opNorm_nonneg _ _ _)) h1

theorem form_dualGram_le {M M' : Matrix n n ℂ} (hM : M.PosDef) (hM' : M'.PosDef) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ y, (form M' y y).re ≤ c * (form M y y).re) (u : n → ℂ) :
    (form (dualGram M) u u).re ≤ c * (form (dualGram M') u u).re := by
  have hu : IsUnit M.det := (isUnit_iff_isUnit_det _).1 hM.isUnit
  have hu' : IsUnit M'.det := (isUnit_iff_isUnit_det _).1 hM'.isUnit
  have hK := posDef_dualGram hM
  have hK' := posDef_dualGram hM'
  have hy : star (Mᵀ *ᵥ (dualGram M *ᵥ star u)) = u := star_mulVec_dualGram hu u
  set y := dualGram M *ᵥ star u
  have h1 : gnorm (dualGram M) u ^ 2 ≤ gnorm (dualGram M') u * gnorm M' y := by
    calc gnorm (dualGram M) u ^ 2 = (form (dualGram M) u u).re := gnorm_sq hK.posSemidef u
      _ = (form (dualGram M) u (star (Mᵀ *ᵥ y))).re := by rw [hy]
      _ = (form (dualGram M') u (star (M'ᵀ *ᵥ y))).re := by
          rw [form_dualGram_star hu, form_dualGram_star hu']
      _ ≤ ‖form (dualGram M') u (star (M'ᵀ *ᵥ y))‖ := Complex.re_le_norm _
      _ ≤ gnorm (dualGram M') u * gnorm (dualGram M') (star (M'ᵀ *ᵥ y)) :=
          norm_form_le hK'.posSemidef _ _
      _ = _ := by rw [gnorm_dualGram_star hM'.isHermitian hu']
  have h2 : gnorm M' y ^ 2 ≤ c * gnorm (dualGram M) u ^ 2 := by
    rw [← hy, gnorm_dualGram_star hM.isHermitian hu, gnorm_sq hM.posSemidef,
      gnorm_sq hM'.posSemidef]
    exact h y
  rw [← gnorm_sq hK.posSemidef, ← gnorm_sq hK'.posSemidef]
  set N := gnorm (dualGram M) u
  set N' := gnorm (dualGram M') u
  set P := gnorm M' y
  have hN : 0 ≤ N := gnorm_nonneg _ _
  have hN' : 0 ≤ N' := gnorm_nonneg _ _
  have hP : 0 ≤ P := gnorm_nonneg _ _
  have h3 : N ^ 2 * N ^ 2 ≤ (c * N' ^ 2) * N ^ 2 := by
    calc N ^ 2 * N ^ 2 ≤ (N' * P) * (N' * P) :=
          mul_le_mul h1 h1 (sq_nonneg _) (mul_nonneg hN' hP)
      _ = N' ^ 2 * P ^ 2 := by ring
      _ ≤ N' ^ 2 * (c * N ^ 2) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = _ := by ring
  rcases (sq_nonneg N).eq_or_lt with h0 | h0
  · rw [← h0]; exact mul_nonneg hc (sq_nonneg _)
  · exact le_of_mul_le_mul_right h3 h0

theorem form_submatrix_equiv (K : Matrix n n ℂ) (e : n ≃ n) (v w : n → ℂ) :
    form (K.submatrix e e) v w = form K (v ∘ e.symm) (w ∘ e.symm) := by
  rw [form, form, submatrix_mulVec_equiv]
  simp only [dotProduct, Function.comp_apply]
  conv_lhs => rw [← Equiv.sum_comp e.symm]
  simp only [Equiv.apply_symm_apply]
  rfl

theorem gnorm_submatrix_equiv (K : Matrix n n ℂ) (e : n ≃ n) (v : n → ℂ) :
    gnorm (K.submatrix e e) v = gnorm K (v ∘ e.symm) := by
  rw [gnorm, gnorm, form_submatrix_equiv]

theorem opNorm_submatrix_equiv_le {K : Matrix n n ℂ} (hK : K.PosDef) (e : n ≃ n)
    (T : Matrix n n ℂ) : opNorm (K.submatrix e e) (K.submatrix e e) (T.submatrix e e) ≤ opNorm K K T :=
  opNorm_le_of_bound (opNorm_nonneg _ _ _) fun v => by
    rw [gnorm_submatrix_equiv, gnorm_submatrix_equiv, submatrix_mulVec_equiv]
    have : ((T *ᵥ (v ∘ e.symm)) ∘ e) ∘ e.symm = T *ᵥ (v ∘ e.symm) := by
      ext i; simp
    rw [this]
    exact gnorm_mulVec_le hK hK.posSemidef T _

end Linear

variable {q : ℕ}

theorem posDef_dualRev {M : Matrix (Fin q) (Fin q) ℂ} (hM : M.PosDef) : (dualRev M).PosDef :=
  (posDef_dualGram hM).submatrix Fin.rev_injective

theorem dualRev_one : dualRev (1 : Matrix (Fin q) (Fin q) ℂ) = 1 := by
  rw [dualRev, dualGram, inv_one, transpose_one]
  exact submatrix_one_equiv Fin.revPerm

theorem opNorm_dualRev_le {M : Matrix (Fin q) (Fin q) ℂ} (hM : M.PosDef)
    (T : Matrix (Fin q) (Fin q) ℂ) :
    opNorm (dualRev M) (dualRev M) ((-Tᵀ).submatrix Fin.rev Fin.rev) ≤ opNorm M M T := by
  have hK := posDef_dualGram hM
  calc opNorm (dualRev M) (dualRev M) ((-Tᵀ).submatrix Fin.rev Fin.rev)
      = opNorm ((dualGram M).submatrix Fin.revPerm Fin.revPerm)
          ((dualGram M).submatrix Fin.revPerm Fin.revPerm) ((-Tᵀ).submatrix Fin.revPerm Fin.revPerm) := rfl
    _ ≤ opNorm (dualGram M) (dualGram M) (-Tᵀ) := opNorm_submatrix_equiv_le hK _ _
    _ ≤ opNorm (dualGram M) (dualGram M) Tᵀ := by
        have := opNorm_smul_le hK hK.posSemidef (-1) Tᵀ
        simpa using this
    _ ≤ opNorm M M T := opNorm_dualGram_transpose_le hM T

section Frame

variable {e : ℕ} {U : Set (Fin e → ℂ)} {H : (Fin e → ℂ) → Matrix (Fin q) (Fin q) ℂ}

theorem isPosFrame_dualRev (h : IsPosFrame U H) : IsPosFrame U fun z => dualRev (H z) :=
  ⟨h.isOpen, fun a b => h.isHermFrame.dual.smooth (Fin.rev a) (Fin.rev b),
    fun z hz => posDef_dualRev (h.posDef z hz)⟩

theorem conn_dualRev {z : Fin e → ℂ} (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (ξ : Fin e → ℂ) :
    conn (fun x => dualRev (H x)) z ξ = (-(conn H z ξ)ᵀ).submatrix Fin.rev Fin.rev := by
  have := conn_submatrix_equiv (fun x => dualGram (H x)) Fin.revPerm z ξ
  rw [conn_dual h hu] at this
  exact this

theorem curv_dualRev {z : Fin e → ℂ} (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det)
    (ξ η : Fin e → ℂ) :
    curv (fun x => dualRev (H x)) z ξ η = (-(curv H z ξ η)ᵀ).submatrix Fin.rev Fin.rev := by
  have := curv_submatrix_equiv (fun x => dualGram (H x)) Fin.revPerm z ξ η
  rw [curv_dual h hu] at this
  exact this

end Frame

theorem dualRev_bounds : ∀ (e q : ℕ) (U : Set (Fin e → ℂ)) (H : (Fin e → ℂ) → Matrix (Fin q) (Fin q) ℂ),
    GlobalTheory.HermFrame.IsPosFrame U H → GlobalTheory.HermFrame.IsPosFrame U (fun z => dualRev (H z)) ∧
    (∀ (G : (Fin e → ℂ) → Matrix (Fin e) (Fin e) ℂ) (C : ℝ),
      GlobalTheory.HermFrame.OneFormBound U (fun _ => (1 : Matrix (Fin q) (Fin q) ℂ)) G (GlobalTheory.HermFrame.conn H) C →
      GlobalTheory.HermFrame.OneFormBound U (fun _ => (1 : Matrix (Fin q) (Fin q) ℂ)) G
        (GlobalTheory.HermFrame.conn fun z => dualRev (H z)) C) ∧
    (∀ (G : (Fin e → ℂ) → Matrix (Fin e) (Fin e) ℂ) (C : ℝ),
      GlobalTheory.HermFrame.TwoFormBound U H G (GlobalTheory.HermFrame.curv H) C →
      GlobalTheory.HermFrame.TwoFormBound U (fun z => dualRev (H z)) G
        (GlobalTheory.HermFrame.curv fun z => dualRev (H z)) C) ∧
    ∀ (H₀ : (Fin e → ℂ) → Matrix (Fin q) (Fin q) ℂ) (r : (Fin e → ℂ) → ℝ) (C : ℝ),
      (∀ z ∈ U, (H₀ z).PosDef) → (∀ z ∈ U, 0 < r z) →
      GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation.PowComparable U r C H₀ H →
      GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation.PowComparable U r C (fun z => dualRev (H₀ z)) (fun z => dualRev (H z)) := by
  intro e q U H hH
  have hF := hH.isHermFrame
  refine ⟨isPosFrame_dualRev hH, fun G C h z hz => ?_, fun G C h z hz => ?_, fun H₀ r C h0 hr hc z hz v => ?_⟩
  · obtain ⟨-, h2, h3⟩ := h z hz
    refine ⟨PosDef.one, h2, fun ξ => ?_⟩
    rw [conn_dualRev (hF.one hz) (hF.isUnit z hz)]
    have := opNorm_dualRev_le (PosDef.one (n := Fin q) (R := ℂ)) (conn H z ξ)
    rw [dualRev_one] at this
    exact this.trans (h3 ξ)
  · obtain ⟨h1, h2, h3⟩ := h z hz
    refine ⟨posDef_dualRev h1, h2, fun ξ η => ?_⟩
    rw [curv_dualRev (hF.two hz) (hF.isUnit z hz)]
    exact (opNorm_dualRev_le h1 _).trans (h3 ξ η)
  · have hp := hr z hz
    have hb : 0 < r z ^ C := Real.rpow_pos_of_pos hp C
    have hneg : r z ^ (-C) = (r z ^ C)⁻¹ := Real.rpow_neg hp.le C
    have hM := hH.posDef z hz
    have hM₀ := h0 z hz
    have hs : ∀ (M : Matrix (Fin q) (Fin q) ℂ) (v : Fin q → ℂ), form (dualRev M) v v =
        form (dualGram M) (v ∘ Fin.revPerm.symm) (v ∘ Fin.revPerm.symm) :=
      fun M v => form_submatrix_equiv (dualGram M) Fin.revPerm v v
    show r z ^ (-C) * (form (dualRev (H₀ z)) v v).re ≤ (form (dualRev (H z)) v v).re ∧
      (form (dualRev (H z)) v v).re ≤ r z ^ C * (form (dualRev (H₀ z)) v v).re
    rw [hs, hs]
    set u := v ∘ Fin.revPerm.symm
    constructor
    · have := form_dualGram_le hM₀ hM hb.le (fun y => (hc z hz y).2) u
      rw [hneg]
      calc (r z ^ C)⁻¹ * (form (dualGram (H₀ z)) u u).re
          ≤ (r z ^ C)⁻¹ * (r z ^ C * (form (dualGram (H z)) u u).re) :=
            mul_le_mul_of_nonneg_left this (inv_nonneg.2 hb.le)
        _ = _ := by field_simp
    · refine form_dualGram_le hM hM₀ hb.le (fun y => ?_) u
      have h1 := (hc z hz y).1
      rw [hneg] at h1
      calc (form (H₀ z) y y).re = r z ^ C * ((r z ^ C)⁻¹ * (form (H₀ z) y y).re) := by
            field_simp
        _ ≤ r z ^ C * (form (H z) y y).re := mul_le_mul_of_nonneg_left h1 hb.le

end GlobalTheory.CurvInterp
