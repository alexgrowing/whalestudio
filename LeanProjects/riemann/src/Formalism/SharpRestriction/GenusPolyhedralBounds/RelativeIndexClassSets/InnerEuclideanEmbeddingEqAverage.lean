import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NormEuclideanEmbeddingEqNetNorm

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module ComplexConjugate

namespace Formalism.MainNotions.Gaps.NetNorms

variable {D : D7} {B : WeightFamilies.Prov D} {j : ℕ} {ka : WeightFamilies.Wt D j}

namespace NetData

variable (Nt : NetData B j ka)

theorem inner_euclideanEmbedding_eq_average (σ : B.KO →+* ℂ) (F G : B.Cusp j ka) :
    inner ℂ (Nt.e0 σ F) (Nt.e0 σ G) =
      (((Fintype.card (Nt.NN σ) : ℝ)⁻¹ : ℝ) : ℂ) * ∑ y, conj (Nt.ev σ y F) * Nt.ev σ y G := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_sigma, Finset.sum_eq_single σ]
  · have hc : (((Fintype.card (Nt.NN σ) : ℝ)⁻¹ : ℝ) : ℂ) = ((Nt.cf σ : ℝ) : ℂ) * ((Nt.cf σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Nt.cf_sq]
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Nt.goodRowsProjector_apply_eq_sum, if_true, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
    ring
  · intro τ _ h
    simp [Nt.goodRowsProjector_apply_eq_sum, h]
  · simp

def herm : Formalism.MainNotions.Gaps.SizeBoundsAlt.Herm (fun σ => Nt.netN σ) (Fintype.card (Σ τ : B.KO →+* ℂ, Nt.NN τ)) where
  e σ := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin (Σ τ : B.KO →+* ℂ, Nt.NN τ))).toLinearEquiv.toLinearMap.comp
    (Nt.e0 σ)
  norm_e σ F := by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.norm_map, Nt.norm_euclideanEmbedding_eq_netNorm]

theorem herm_inner (σ : B.KO →+* ℂ) (F G : B.Cusp j ka) :
    inner ℂ (Nt.herm.e σ F) (Nt.herm.e σ G) = inner ℂ (Nt.e0 σ F) (Nt.e0 σ G) := by
  simp only [herm, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.inner_map_map]

theorem herm_conj : Nt.herm.Conj := by
  intro σ f g
  rw [Nt.herm_inner, Nt.herm_inner, Nt.inner_euclideanEmbedding_eq_average, Nt.inner_euclideanEmbedding_eq_average]
  rw [← Fintype.card_congr (Nt.cj σ), ← (Nt.cj σ).sum_comp]
  simp only [Nt.ev_conj, Complex.conj_conj, star_mul', Complex.star_def, Complex.conj_ofReal, map_sum, map_mul]

end NetData

theorem sup_L2_bound_of_net : SupL2BoundFromNet (D := D) (B := B) (j := j) (ka := ka) := by
  intro Nt hM hL large₂ CG AG hP F σ
  rw [Nt.Bp_L2N_run hM hL]
  change B.supN j ka σ F ^ 2 ≤ _ * Nt.netN σ F ^ 2
  obtain ⟨y, hy⟩ := hM σ F
  have hS := B.supN_nonneg j ka σ F
  have hn : (1 : ℝ) ≤ (Fintype.card (Nt.NN σ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨y⟩).ne'
  have hsum0 : (0 : ℝ) ≤ ∑ y, ‖Nt.ev σ y F‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : Nt.netN σ F ^ 2 = (Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2 :=
    Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr (by linarith)) hsum0)
  have h1 : ‖Nt.ev σ y F‖ ^ 2 ≤ ∑ y, ‖Nt.ev σ y F‖ ^ 2 :=
    Finset.single_le_sum (f := fun y => ‖Nt.ev σ y F‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ y)
  have h2 : (B.supN j ka σ F / 4) ^ 2 ≤ ‖Nt.ev σ y F‖ ^ 2 := pow_le_pow_left₀ (by positivity) hy 2
  have h3 : B.supN j ka σ F ^ 2 ≤ 16 * (Fintype.card (Nt.NN σ) : ℝ) * Nt.netN σ F ^ 2 := by
    rw [hsq]
    have : 16 * (Fintype.card (Nt.NN σ) : ℝ) * ((Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2) =
        16 * ∑ y, ‖Nt.ev σ y F‖ ^ 2 := by
      field_simp
    rw [this]
    have h4 : (B.supN j ka σ F / 4) ^ 2 = B.supN j ka σ F ^ 2 / 16 := by ring
    linarith
  have h4 : 16 * (Fintype.card (Nt.NN σ) : ℝ) ≤ Real.exp (WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size)) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 16 * (Fintype.card (Nt.NN σ) : ℝ))]
    exact Real.exp_le_exp.mpr (hP σ)
  calc B.supN j ka σ F ^ 2 ≤ 16 * (Fintype.card (Nt.NN σ) : ℝ) * Nt.netN σ F ^ 2 := h3
    _ ≤ Real.exp (WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size)) * Nt.netN σ F ^ 2 :=
      mul_le_mul_of_nonneg_right h4 (sq_nonneg _)

theorem deepHermNet : DeepHermNetSt (D := D) (B := B) (j := j) (ka := ka) := by
  intro P Nt hM hL X
  exact ⟨_, { e := Nt.herm.e, norm_e := fun σ F => (Nt.herm.norm_e σ F).trans (by rw [Nt.Bp_L2N_run hM hL]) },
    Nt.herm_conj⟩

theorem deepLogDNet : DeepLogDNetSt (D := D) (B := B) (j := j) (ka := ka) := by
  intro P Nt hM hL X σ Pd hI hP
  change Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd
  have hd : finrank B.KO (B.Cusp j ka) ≤ Fintype.card (Nt.NN σ) := by
    have hb := hI _ _ (Module.finBasis B.KO (B.Cusp j ka)).linearIndependent
    have := hb.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using this
  have hlog0 : 0 ≤ Real.log (Fintype.card (Nt.NN σ) : ℝ) := Real.log_natCast_nonneg _
  rcases Nat.eq_zero_or_pos (finrank B.KO (B.Cusp j ka)) with h0 | h0
  · rw [h0]
    simp only [Nat.cast_zero, Real.log_zero]
    linarith
  · calc Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Real.log (Fintype.card (Nt.NN σ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hd)
      _ ≤ Pd := hP

end Formalism.MainNotions.Gaps.NetNorms
