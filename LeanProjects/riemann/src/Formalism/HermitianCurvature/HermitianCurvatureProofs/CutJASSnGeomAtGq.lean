import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Matrix Formalism.REAL Formalism.QuantumDeterminants PI.UnitaryGroupMassFormula.GsFr
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ}

theorem unitH_smul (a : ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    unitH k r (a • v) = (a / ((‖a‖ : ℝ) : ℂ)) • unitH k r v := by
  unfold unitH
  have h1 : (herm (Hpk k r) (a • v) (a • v)).re = Complex.normSq a * (herm (Hpk k r) v v).re := by
    rw [hm_smul_l, hm_smul_r, ← mul_assoc, Complex.star_def, Complex.mul_conj, Complex.re_ofReal_mul]
  rw [h1, Real.sqrt_mul (Complex.normSq_nonneg a), mul_inv]
  simp only [smul_smul]
  congr 1
  have hn : Real.sqrt (Complex.normSq a) = ‖a‖ := by
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg a)]
  rw [hn]
  push_cast
  ring

theorem prWv_eq (z v : Fin (2 * r + k + 1) → ℂ) : prWv k r z v = prW k r z v := rfl

theorem prW_smul (z : Fin (2 * r + k + 1) → ℂ) (a : ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    prW k r z (a • v) = a • prW k r z v := by
  rw [← Pm_mulVec, ← Pm_mulVec, mulVec_smul]

def dq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Fin (r + 1) → ℂ := fun a =>
  if h : a.val < r then c ⟨a.val, h⟩ else herm (Hpk k r) (bigCell k r c μ *ᵥ z') z

theorem prod_erase_dq (z z' : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    ∏ j ∈ Finset.univ.erase (Fin.last r), dq k r z z' c μ j = ∏ i, c i := by
  rw [← Finset.filter_ne' Finset.univ (Fin.last r), Finset.prod_filter, Fin.prod_univ_castSucc]
  simp only [ne_eq, Fin.castSucc_ne_last, not_false_eq_true, if_true, not_true_eq_false, if_false, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [dq]

theorem adj_zhat (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') (c : Fin r → ℂ)
    (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (a b : Fin (r + 1)) :
    (Zhat k r z z' (bigCell k r c μ)).adjugate a b =
      if a = b then ∏ j ∈ Finset.univ.erase a, dq k r z z' c μ j else 0 := by
  rw [big_cell_coordinate_holds k r z z' c μ hz hz']
  have e : (Matrix.diagonal fun a : Fin (r + 1) =>
      if h : a.val < r then c ⟨a.val, h⟩ else herm (Hpk k r) (bigCell k r c μ *ᵥ z') z) =
      Matrix.diagonal (dq k r z z' c μ) := rfl
  rw [e, Matrix.adjugate_diagonal, Matrix.diagonal_apply]

theorem xcof_gq (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') (c : Fin r → ℂ)
    (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    xcof k r z z' (bigCell k r c μ) = (∏ i, c i) • (bigCell k r c μ *ᵥ z') := by
  unfold xcof
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [adj_zhat z z' hz hz' c μ, if_pos rfl, prod_erase_dq, fv_last]
  · intro b _ hb
    rw [adj_zhat z z' hz hz' c μ, if_neg hb, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem xcofL_gq (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') (c : Fin r → ℂ)
    (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    xcofL k r z z' (bigCell k r c μ) = star (∏ i, c i) • z := by
  unfold xcofL
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [adj_zhat z z' hz hz' c μ, if_pos rfl, prod_erase_dq, fv_last]
  · intro b _ hb
    rw [adj_zhat z z' hz hz' c μ, if_neg (Ne.symm hb), star_zero, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

section gq

variable (z z' : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)

theorem gq_wb {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    bigCell k r c μ *ᵥ v = B2.embWb k r μ *ᵥ v := by
  rw [(Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).2, ← mulVec_mulVec, Formalism.FourierDecayAlt.P.BigCellDecomposition.bigCell_one_fixes_vector hv c]

theorem jV_inWb (u : Fin (k + 1) → ℂ) : inWb k r (Formalism.FourierDecayAlt.P.TwoByOneBlock.jV k r u) := by
  intro i hi
  apply Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_out
  intro h
  rcases hi with hi | hi <;> omega

theorem Hb_sq : Hb k * Hb k = 1 := by
  rw [Hb, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

theorem isUnit_mu {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : μᴴ * Hb k * μ = Hb k) : IsUnit μ.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hb k * μᴴ * Hb k)
  rw [show Hb k * μᴴ * Hb k * μ = Hb k * (μᴴ * Hb k * μ) by simp only [Matrix.mul_assoc], h, Hb_sq]

theorem isUnit_emb {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hc : ∀ a, c a ≠ 0) (h : μᴴ * Hb k * μ = Hb k) :
    IsUnit (B2.embWb k r μ).det := by
  have hg := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh (big_cell_mem_holds k r c μ hc h)
  rw [(Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).2, det_mul] at hg
  exact isUnit_of_mul_isUnit_left hg

def wq (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Fin (2 * r + k + 1) → ℂ :=
  Formalism.FourierDecayAlt.P.TwoByOneBlock.jV k r (μ⁻¹ *ᵥ Formalism.QuantumDeterminants.wbPart k r z)

theorem gq_wq {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hz : inWb k r z) (h : μᴴ * Hb k * μ = Hb k) :
    bigCell k r c μ *ᵥ wq k r z μ = z := by
  unfold wq
  rw [Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV, mulVec_mulVec, mul_nonsing_inv _ (isUnit_mu h), one_mulVec,
    Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hz]

theorem emb_wq {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hz : inWb k r z) (h : μᴴ * Hb k * μ = Hb k) :
    B2.embWb k r μ *ᵥ wq k r z μ = z := by
  rw [← gq_wb (fun _ => (1 : ℂ)) μ (show inWb k r (wq k r z μ) from jV_inWb _), gq_wq z (fun _ => (1 : ℂ)) hz h]

theorem embedded_inverse_mul_vec {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hc : ∀ a, c a ≠ 0) (hz : inWb k r z)
    (h : μᴴ * Hb k * μ = Hb k) : (B2.embWb k r μ)⁻¹ *ᵥ z = wq k r z μ := by
  conv_lhs => rw [← emb_wq z hz h]
  rw [mulVec_mulVec, nonsing_inv_mul _ (isUnit_emb c hc h), one_mulVec]

theorem big_cell_inverse_mul_vec {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hc : ∀ a, c a ≠ 0) (hz : inWb k r z)
    (h : μᴴ * Hb k * μ = Hb k) : (bigCell k r c μ)⁻¹ *ᵥ z = wq k r z μ := by
  conv_lhs => rw [← gq_wq z c hz h]
  rw [mulVec_mulVec, nonsing_inv_mul _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh (big_cell_mem_holds k r c μ hc h)), one_mulVec]

end gq

theorem nuG_gq {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (c : Fin r → ℂ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ) :
    nuG z z' (bigCell k r c (μsec ζ)) = phD c • nu0 k r z z' μsec ζ := by
  unfold nuG omW nu0
  rw [xcof_gq z z' hz hz' c, prW_smul, unitH_smul, gq_wb c _ hz', prWv_eq]
  rfl

theorem nuG'_gq {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {c : Fin r → ℂ}
    (hc : ∀ a, c a ≠ 0) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ)
    (h : (μsec ζ)ᴴ * Hb k * μsec ζ = Hb k) :
    nuG' z z' (bigCell k r c (μsec ζ)) = conj (phD c) • nu0' k r z z' μsec ζ := by
  unfold nuG' omW' nu0'
  rw [xcofL_gq z z' hz hz' c, mulVec_smul, prW_smul, unitH_smul, big_cell_inverse_mul_vec z c hc hz h, prWv_eq]
  unfold NF.muZ
  rw [embedded_inverse_mul_vec z c hc hz h]
  congr 1
  unfold phD
  rw [map_div₀, Complex.conj_ofReal, Complex.star_def, Complex.norm_conj]

theorem phD_norm {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) : ‖phD c‖ = 1 := by
  have hP : (∏ i, c i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hc a
  unfold phD
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.2 hP)

theorem star_mul_self_of_norm {l : ℂ} (h : ‖l‖ = 1) : star l * l = 1 := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
  norm_num

theorem herm_self_real (p : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) p p = (((herm (Hpk k r) p p).re : ℝ) : ℂ) := by
  conv_lhs => rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq]
  unfold Tz
  push_cast
  ring

theorem PpG_gq {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {c : Fin r → ℂ}
    (hc : ∀ a, c a ≠ 0) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ)
    (h : (μsec ζ)ᴴ * Hb k * μsec ζ = Hb k) (v : Fin (2 * r + k + 1) → ℂ) :
    PpG z z' (bigCell k r c (μsec ζ)) *ᵥ v =
      prW k r z' v - herm (Hpk k r) (prW k r z' v) (nu0' k r z z' μsec ζ) • nu0' k r z z' μsec ζ := by
  unfold PpG
  rw [sub_mulVec, ← mulVec_mulVec, Pm_mulVec, Rk_mulVec, nuG'_gq hz hz' hc μsec ζ h, hm_smul_r, smul_smul]
  congr 1
  have hl : star (conj (phD c)) * conj (phD c) = 1 :=
    star_mul_self_of_norm (by rw [Complex.norm_conj, phD_norm hc])
  rw [show star (conj (phD c)) * herm (Hpk k r) (prW k r z' v) (nu0' k r z z' μsec ζ) * conj (phD c) =
    (star (conj (phD c)) * conj (phD c)) * herm (Hpk k r) (prW k r z' v) (nu0' k r z z' μsec ζ) by ring, hl, one_mul]

theorem unitH_eq (p : Fin (2 * r + k + 1) → ℂ) :
    unitH k r p = (((Real.sqrt (herm (Hpk k r) p p).re)⁻¹ : ℝ) : ℂ) • p := rfl

theorem u_perp {z' : Fin (2 * r + k + 1) → ℂ} (hz' : C2.StdZ k r z') {w p : Fin (2 * r + k + 1) → ℂ}
    (hp : p ∈ Wsp k r z') :
    herm (Hpk k r) (w - herm (Hpk k r) w (unitH k r p) • unitH k r p) p = 0 := by
  by_cases hp0 : p = 0
  · subst hp0; simp [herm]
  have hpos := posV hz' hp.1 hp.2 hp0
  set s := (herm (Hpk k r) p p).re with hs
  rw [unitH_eq, hm_sub_l, hm_smul_l, hm_smul_l, hm_smul_r, herm_self_real p, ← hs]
  simp only [Complex.ofReal_re]
  have hss : (Real.sqrt s)⁻¹ * (Real.sqrt s)⁻¹ * s = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  have hst : star (((Real.sqrt s)⁻¹ : ℝ) : ℂ) = (((Real.sqrt s)⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [hst]
  have : ((((Real.sqrt s)⁻¹ : ℝ) : ℂ) * herm (Hpk k r) w p) * ((((Real.sqrt s)⁻¹ : ℝ) : ℂ) * ((s : ℝ) : ℂ)) =
      (((Real.sqrt s)⁻¹ * (Real.sqrt s)⁻¹ * s : ℝ) : ℂ) * herm (Hpk k r) w p := by push_cast; ring
  rw [this, hss]
  push_cast
  ring

theorem ioG_gq {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {c : Fin r → ℂ}
    (hc : ∀ a, c a ≠ 0) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ)
    (h : (μsec ζ)ᴴ * Hb k * μsec ζ = Hb k) :
    ioG z z' (bigCell k r c (μsec ζ)) = io0 k r z z' μsec ζ := by
  set g := bigCell k r c (μsec ζ) with hgdef
  have hg : g ∈ B.GV k r := big_cell_mem_holds k r c _ hc h
  have hp : nu0' k r z z' μsec ζ = unitH k r (prW k r z' (wq k r z (μsec ζ))) := by
    unfold nu0'; rw [prWv_eq]; unfold NF.muZ; rw [embedded_inverse_mul_vec z c hc hz.1 h]
  have hpW : prW k r z' (wq k r z (μsec ζ)) ∈ Wsp k r z' := prW_mem hz' _

  have key : ∀ v : Fin (2 * r + k + 1) → ℂ,
      ioG z z' g *ᵥ v = NF.muZ k r μsec ζ *ᵥ
        (prW k r z' v - herm (Hpk k r) (prW k r z' v) (nu0' k r z z' μsec ζ) • nu0' k r z z' μsec ζ) := by
    intro v
    set u := prW k r z' v - herm (Hpk k r) (prW k r z' v) (nu0' k r z z' μsec ζ) • nu0' k r z z' μsec ζ with hu
    have huW : u ∈ Wsp k r z' := by
      refine Wsp_sub (prW_mem hz' v) (Wsp_smul _ ?_)
      rw [hp, unitH_eq]; exact Wsp_smul _ hpW
    have huwq : herm (Hpk k r) u (wq k r z (μsec ζ)) = 0 := by
      rw [← herm_prW_r huW, hu, hp]
      exact u_perp hz' hpW
    have hgu_wb : inWb k r (g *ᵥ u) := by
      rw [← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart huW.1, hgdef, Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV]
      exact jV_inWb _
    have hguz : herm (Hpk k r) (g *ᵥ u) z = 0 := by
      rw [← gq_wq z c hz.1 h, ← hgdef, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hg, huwq]
    have hwv : wv k r z g u = 0 := by
      funext a
      show herm (Hpk k r) (g *ᵥ u) (fvec k r z a) = 0
      by_cases ha : a = Fin.last r
      · rw [ha, fv_last]; exact hguz
      · exact herm_wb_X (fv_X z a ha) (wb_hi hgu_wb)
    have hgam : gam k r z z' g u = 0 := by
      simp [gam, hwv]
    have hL : Lm k r z z' g *ᵥ u = u := by
      rw [Lm_mulVec, hgam]; simp
    unfold ioG
    rw [← mulVec_mulVec, PpG_gq hz.1 hz'.1 hc μsec ζ h, ← hu, Phi_mulVec, hL, prW_of_mem ⟨hgu_wb, hguz⟩,
      hgdef, gq_wb c _ huW.1]
    rfl
  ext i j
  have e1 : ioG z z' g i j = (ioG z z' g *ᵥ Pi.single j 1) i := by
    rw [Matrix.mulVec_single_one]; rfl
  rw [e1, key]
  unfold io0
  rw [Matrix.of_apply, prWv_eq]

theorem geometry_at_level_function : GeomAtGq := by
  intro k r z z' μsec _ hz hz' hsec c ζ hc hζ
  have h := (hsec.2 ζ hζ).1
  exact ⟨nuG_gq hz.1 hz'.1 c μsec ζ, nuG'_gq hz.1 hz'.1 hc μsec ζ h, ioG_gq hz hz' hc μsec ζ h⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
