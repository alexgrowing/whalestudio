import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.NormScale

theorem deg_scale : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N N' : (K →+* ℂ) → V → ℝ) (t : (K →+* ℂ) → ℝ), HasGram N → (∀ σ, 0 < t σ) → (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → (∀ σ x, N' σ x = t σ * N σ x) → HasGram N' ∧ ∀ L : Submodule (𝓞 K) V, L.FG → deg N' L = deg N L - (Formalism.HN.rkK L : ℝ) * ((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) := by
  intro K V _ _ _ _ _ _ _ N N' t hN ht hc hN'
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  set X' : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ := fun v => ((t v.embedding : ℂ)⁻¹) • X v with hX'
  have htc : ∀ v : InfinitePlace K, (t v.embedding : ℂ) ≠ 0 := fun v => by
    exact_mod_cast (ht v.embedding).ne'
  have hinv : ∀ v, (X' v)⁻¹ = (t v.embedding : ℂ) • (X v)⁻¹ := fun v => by
    refine Matrix.inv_eq_left_inv ?_
    simp only [hX', Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ (hG v).1,
      inv_mul_cancel₀ (htc v), one_smul]
  have hfc : ∀ v x, Formalism.HermitianLatticesTheory.fcoord b X' v x = (t v.embedding : ℂ) • Formalism.HermitianLatticesTheory.fcoord b X v x := fun v x => by
    simp only [Formalism.HermitianLatticesTheory.fcoord, hinv]
    exact Matrix.smul_mulVec _ _ _
  have hnorm : ∀ v x, Formalism.HermitianLatticesTheory.normAt b X' v x = t v.embedding * Formalism.HermitianLatticesTheory.normAt b X v x := fun v x => by
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, hfc, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
      ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (ht _)]
  have hG' : IsGram b X' N' := fun v => by
    refine ⟨?_, fun x => by rw [hnorm, (hG v).2, hN']⟩
    simp only [hX', Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 (inv_ne_zero (htc v)))).mul (hG v).1
  refine ⟨hG'.hasGram, fun L hL => ?_⟩
  have hgram : ∀ v {j : ℕ} (e : Fin j → V), Formalism.HN.gramPl b X' v e = (((t v.embedding) ^ 2 : ℝ) : ℂ) • Formalism.HN.gramPl b X v e := by
    intro v j e
    ext a c
    simp only [Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, hfc, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, star_mul', Complex.star_def, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  have hdet : ∀ v {j : ℕ} (e : Fin j → V), (Formalism.HN.gramPl b X' v e).det.re =
      t v.embedding ^ (2 * j) * (Formalism.HN.gramPl b X v e).det.re := by
    intro v j e
    rw [hgram, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul, ← pow_mul]
  haveI : Module.Finite K V := Module.Finite.of_basis b
  obtain ⟨e, heL, hsp, he⟩ := Submodule.exists_fun_fin_finrank_span_eq K (L : Set V)
  have hj : Formalism.HN.rkK L = Module.finrank K (Submodule.span K (L : Set V)) := rfl
  generalize Module.finrank K (Submodule.span K (L : Set V)) = j at e heL hsp he hj
  obtain ⟨-, g1, m1⟩ := GlobalTheory.SlopeExt.rk_mul_mu_eq b X (fun v => (hG v).1) e he L hL
    (Submodule.span_le.2 (Set.range_subset_iff.2 heL)) hj
  obtain ⟨-, g2, m2⟩ := GlobalTheory.SlopeExt.rk_mul_mu_eq b X' (fun v => (hG' v).1) e he L hL
    (Submodule.span_le.2 (Set.range_subset_iff.2 heL)) hj
  have hlog : ∀ v, Real.log (Formalism.HN.gramPl b X' v e).det.re =
      (2 * j : ℝ) * Real.log (t v.embedding) + Real.log (Formalism.HN.gramPl b X v e).det.re := fun v => by
    rw [hdet, Real.log_mul (pow_pos (ht _) _).ne' (g1 v).ne', Real.log_pow]
    push_cast; ring
  have hsum : ∑ σ : K →+* ℂ, Real.log (t σ) = 2 * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by
    rw [← GlobalTheory.SlopeExt.sum_mk K (fun v => Real.log (t v.embedding))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]; exact congrArg Real.log (hc σ).symm
  have hfin : (Module.finrank ℚ K : ℝ) = 2 * Formalism.HN.nPl K := by
    have := GlobalTheory.SlopeExt.sum_mk K (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    rw [← NumberField.Embeddings.card K ℂ, this]
    rfl
  have hP : (Formalism.HN.nPl K : ℝ) ≠ 0 := by exact_mod_cast Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.nPl_ne_zero
  rw [Finset.sum_congr rfl (fun v _ => hlog v), Finset.sum_add_distrib, ← Finset.mul_sum] at m2
  simp only [GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope, slope_sq_eq hG hL, slope_sq_eq hG' hL, hj, hsum, hfin]
  have key : (Formalism.HN.nPl K : ℝ) * ((j : ℝ) * Formalism.HN.muDef b X' L) = (Formalism.HN.nPl K : ℝ) * ((j : ℝ) * Formalism.HN.muDef b X L)
      - 2 * j * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by linarith
  field_simp
  linear_combination key

end GlobalTheory.NormScale
