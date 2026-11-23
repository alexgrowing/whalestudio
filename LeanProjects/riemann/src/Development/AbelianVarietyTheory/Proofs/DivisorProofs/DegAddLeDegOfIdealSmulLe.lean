import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.TwistIdeal

theorem htMap_le {K V W ι κ : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {b : Module.Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ} {b' : Module.Basis κ K W}
    {X' : InfinitePlace K → Matrix κ κ ℂ} {N : (K →+* ℂ) → V → ℝ} {N' : (K →+* ℂ) → W → ℝ}
    (hG : IsGram b X N) (hG' : IsGram b' X' N') (φ : V →ₗ[K] W) (hφ : φ ≠ 0) (t : (K →+* ℂ) → ℝ)
    (ht : ∀ σ, 0 < t σ) (htc : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (hN : ∀ σ x, N' σ (φ x) ≤ t σ * N σ x) :
    Formalism.HN.htMap b X b' X' φ ≤ 2 * (∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ) := by
  have hop : ∀ v : InfinitePlace K, Formalism.HN.opNormAt b X b' X' v φ ^ 2 ≤ t v.embedding ^ 2 := fun v =>
    opNormAt_sq_le b X b' X' (fun v => (hG v).1) v (IsTotallyComplex.isComplex v) φ _ (sq_nonneg _) fun x => by
      rw [← normAt_sq_eq_majAt, ← normAt_sq_eq_majAt, (hG v).2, (hG' v).2, ← mul_pow]
      exact pow_le_pow_left₀ (normAt_nonneg _ _ _ _ |>.trans_eq ((hG' v).2 _)) (hN _ _) 2
  have hpos : ∀ v : InfinitePlace K, 0 < Formalism.HN.opNormAt b X b' X' v φ := fun v =>
    Formalism.HN.PlaceOperatorNorms.opNormAt_pos b X b' X' (fun v => (hG v).1) (fun v => (hG' v).1) v φ hφ
  have hs : ∑ σ : K →+* ℂ, Real.log (t σ) = 2 * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by
    rw [← GlobalTheory.SlopeExt.sum_mk K fun v => Real.log (t v.embedding)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]
      have e : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
        RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
      rw [e, htc σ]
  have hd : (Module.finrank ℚ K : ℝ) = 2 * Formalism.HN.nPl K := by
    have := GlobalTheory.SlopeExt.sum_mk K fun _ => (1 : ℝ)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Embeddings.card] at this
    rw [this]; rfl
  have hn : (0 : ℝ) < Formalism.HN.nPl K := by
    have : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
    linarith
  unfold Formalism.HN.htMap
  rw [hs, hd]
  have hsum : ∑ v, Real.log (Formalism.HN.opNormAt b X b' X' v φ ^ 2) ≤ ∑ v : InfinitePlace K, 2 * Real.log (t v.embedding) :=
    Finset.sum_le_sum fun v _ => by
      have := Real.log_le_log (pow_pos (hpos v) 2) (hop v)
      rw [Real.log_pow, Real.log_pow] at this
      rw [Real.log_pow]
      push_cast at this ⊢
      exact this
  rw [← Finset.mul_sum] at hsum
  rw [one_div, inv_mul_le_iff₀ hn]
  have : 2 * (2 * ∑ v : InfinitePlace K, Real.log (t v.embedding)) / (2 * (Formalism.HN.nPl K : ℝ)) * Formalism.HN.nPl K =
      2 * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by
    field_simp
  linarith

end GlobalTheory.TwistIdeal

namespace GlobalTheory.TwistIdeal

theorem deg_add_le_deg_of_ideal_smul_le : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (N : (K →+* ℂ) → V → ℝ) (N' : (K →+* ℂ) → W → ℝ) (φ : V →ₗ[K] W) (t : (K →+* ℂ) → ℝ) (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) W) (𝔞 : Ideal (𝓞 K)), HasGram N → HasGram N' → Function.Injective φ → (∀ σ, 0 < t σ) → (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → (∀ σ x, N' σ (φ x) ≤ t σ * N σ x) → L.FG → L'.FG → 𝔞 ≠ ⊥ → 𝔞 • L.map (φ.restrictScalars (𝓞 K)) ≤ L' → Formalism.HN.rkK L' = Formalism.HN.rkK L → deg N L + (Formalism.HN.rkK L : ℝ) * (-((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) - Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ)) ≤ deg N' L' := by
  intro K V _ _ _ _ _ _ _ W _ _ _ _ N N' φ t L L' 𝔞 hN hN' hinj htpos htc hNb hL hL' h𝔞 hsub hrk
  by_cases h0 : L = ⊥
  · subst h0
    have h1 : Formalism.HN.rkK (⊥ : Submodule (𝓞 K) V) = 0 := by simp [Formalism.HN.rkK]
    rw [h1] at hrk
    simp [deg, h1, hrk]
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  obtain ⟨⟨n', ⟨b', X'⟩, hG'⟩⟩ := hN'
  letI : StarRing K := starRingOfComm
  have hI : ((𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔞
  have hsm : Formalism.HermitianLatticesTheory.idealSmul (((𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) : Submodule (𝓞 K) K)
      (L.map (φ.restrictScalars (𝓞 K))) ≤ L' := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨a, ha, x, hx, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal (S := (nonZeroDivisors (𝓞 K))) (P := K)).1 ha
    rw [algebraMap_smul]
    exact hsub (Submodule.smul_mem_smul hr hx)
  have key := Formalism.ExtensionFiltration.twistLower K V (Fin n) W (Fin n') b X b' X' (fun v => (hG v).1) (fun v => (hG' v).1)
    φ L L' (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) hI hL hL' h0 hinj hsm hrk
  have hφ : φ ≠ 0 := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    exact hx0 (hinj (by rw [h, map_zero, LinearMap.zero_apply]))
  have hht := htMap_le hG hG' φ hφ t htpos htc hNb
  rw [FractionalIdeal.coeIdeal_absNorm] at key
  have hb : slope_sq N L / 2 - (∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ) -
      Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) ≤ slope_sq N' L' / 2 := by
    rw [slope_sq_eq hG hL, slope_sq_eq hG' hL']
    have e1 : 2 * (∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ) =
        2 * ((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) := by ring
    have e2 : 2 * Real.log ((Ideal.absNorm 𝔞 : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) =
        2 * (Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ)) := by push_cast; ring
    rw [e1] at hht
    rw [e2] at key
    linarith
  have hr : (0 : ℝ) ≤ Formalism.HN.rkK L := Nat.cast_nonneg _
  unfold deg GlobalTheory.AllWt.slope
  rw [hrk]
  nlinarith [mul_le_mul_of_nonneg_left hb hr]

end GlobalTheory.TwistIdeal
