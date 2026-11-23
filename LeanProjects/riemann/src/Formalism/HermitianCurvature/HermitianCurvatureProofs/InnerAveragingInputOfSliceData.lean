import Formalism.HermitianCurvature.OrbitalIntegralDiagonalSlice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChangeOfVariablesXy
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DensityLemmaOfReductions
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThresholdOfLargeConstant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnitriangularEqOneOfMinorsNonzero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InnerDensityOfAveraging
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AveragingVanishes
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerSplit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerPairs

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6 Formalism.FourierDecayAlt.DensityAveraging Formalism.FourierDecayAlt.OrbitalSlices

theorem norm_eq_of_pow_eq_same {s : ℕ} (hs : 0 < s) {a z z₀ : ℂ} (hz : z ^ s = a) (hz₀ : z₀ ^ s = a) : ‖z‖ = ‖z₀‖ := by
  have h : ‖z‖ ^ s = ‖z₀‖ ^ s := by rw [← norm_pow, ← norm_pow, hz, hz₀]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hs.ne').mp h

theorem mem_rootSet_iff_pow_eq {s : ℕ} (hs : 0 < s) {a z : ℂ} : z ∈ G.rootSet s a ↔ z ^ s = a := by
  rw [G.rootSet, Multiset.mem_toFinset, Polynomial.mem_nthRoots hs]

theorem germ_leading_term_root_sum {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ)
    (Ψ : G.Mat (m + 1 + 1) → V) (t Dd z₀ : ℂ) (hz₀ : z₀ ^ (m + 2) = (-1) ^ (m + 3) * Dd) :
    G.mainTerm β m (fun _ => 1) Ψ t Dd =
      (((m : ℂ) + 2)⁻¹ * ((‖z₀‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ)) •
        ∑ z ∈ G.rootSet (m + 2) ((-1) ^ (m + 3) * Dd), G.psi β (((m : ℂ) + 2) * z / t) • G.OmLong β (m + 1) Ψ z := by
  unfold G.mainTerm
  rw [mul_smul]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [mem_rootSet_iff_pow_eq (by omega)] at hz
  rw [norm_eq_of_pow_eq_same (by omega) hz hz₀, mul_one, mul_smul]

def germDecayRateAt (C₁ C₂ : ℕ) : Prop :=
  ∀ (m : ℕ) (β : ℂ), β ≠ 0 → ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc →
    ∃ Cst : ℝ, ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
      (Φ : G.Mat (m + 1 + 1) → V) (A K : ℝ) (k : ℕ),
      (C₁ : ℝ) * ((m : ℝ) + 2) ^ 2 ≤ A → C₂ * (m + 2) ^ 2 ≤ k →
      G.DerivBound k (G.detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ →
      ∀ t c : ℂ, t ≠ 0 → c * t ^ (m + 1) ∈ Kc → ‖G.remainder β m (fun _ => 1) Φ t c‖ ≤ Cst * K * ‖t‖

theorem averaging_datum_of_slice_point {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {D : B.RealPlaceData k r Wp Wq} {F' : B.Mat k r → (Wq →L[ℂ] Wp)} {γ : B.Mat k r}
    {C₁ C₂ : ℕ} (hR : germDecayRateAt C₁ C₂) (S : SlicePt D F' γ) (hS : S.Good C₁ C₂) :
    ∃ T : AvgDatum D F' γ, MoreBlocks D F' γ → T.GermBound := by
  obtain ⟨A, K, kk, hA, hk, hDec, hL, hDg, hRel⟩ := hS
  unfold SlicePt.Decay at hDec
  unfold SlicePt.OrbitalIntegralLongElement at hL
  unfold SlicePt.OrbitalIntegralDiagonalSlice at hDg
  unfold SlicePt.DiagRel at hRel
  unfold germDecayRateAt at hR
  have hz₀ : S.z₀ ∈ G.rootSet (S.m + 2) ((-1) ^ (S.m + 3) * S.Dd) :=
    (mem_rootSet_iff_pow_eq (by omega)).mpr S.z₀_pow
  let R := G.rootSet (S.m + 2) ((-1) ^ (S.m + 3) * S.Dd)
  let e := R.equivFin
  have hm2 : ((S.m : ℂ) + 2) ≠ 0 := by
    have h : ((S.m + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using h
  have hinj : Function.Injective (fun j : Fin R.card => ((S.m : ℂ) + 2) * (e.symm j : ℂ)) := by
    intro i j hij
    exact e.symm.injective.eq_iff.mp (Subtype.ext (mul_left_cancel₀ hm2 hij))
  have htie : ‖G.OmLong S.β (S.m + 1) S.Ψ (e.symm (e ⟨S.z₀, hz₀⟩) : ℂ)‖ = 0 → VanAt D F' γ := by
    intro h0
    rw [e.symm_apply_apply, norm_eq_zero] at h0
    unfold VanAt
    intro O
    rw [hL O]
    exact h0
  refine ⟨⟨Wq →L[ℂ] Wp, normSeminorm ℂ (Wq →L[ℂ] Wp), S.β, S.β_ne, R.card,
    fun j => ((S.m : ℂ) + 2) * (e.symm j : ℂ), hinj, fun j => G.OmLong S.β (S.m + 1) S.Ψ (e.symm j : ℂ),
    e ⟨S.z₀, hz₀⟩, htie⟩, ?_⟩
  · intro hMB
    unfold MoreBlocks at hMB
    unfold AvgDatum.GermBound
    dsimp only
    obtain ⟨Cst, hCst⟩ := hR S.m S.β S.β_ne {S.Dd} isCompact_singleton
      (fun h => S.Dd_ne (Set.mem_singleton_iff.mp h).symm)
    have hz0ne : S.z₀ ≠ 0 := by
      intro h
      have hp := S.z₀_pow
      rw [h, zero_pow (by omega)] at hp
      exact S.Dd_ne (by simpa using hp.symm)
    have hc0 : ((S.m : ℂ) + 2)⁻¹ * ((‖S.z₀‖ ^ ((S.m + 1) ^ 2) : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (inv_ne_zero hm2) (Complex.ofReal_ne_zero.mpr (pow_pos (norm_pos_iff.mpr hz0ne) _).ne')
    refine ⟨Cst * K / ‖((S.m : ℂ) + 2)⁻¹ * ((‖S.z₀‖ ^ ((S.m + 1) ^ 2) : ℝ) : ℂ)‖, 2 / S.δ, fun x hx => ?_⟩
    have hδ := S.δ_pos
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le (by positivity) hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp hxpos
    have htδ : ‖x⁻¹‖ < S.δ := by
      rw [norm_inv, inv_lt_comm₀ hxpos hδ]
      calc S.δ⁻¹ < 2 / S.δ := by rw [div_eq_mul_inv]; linarith [inv_pos.mpr hδ]
        _ ≤ ‖x‖ := hx
    have hct : S.Dd * x ^ (S.m + 1) * x⁻¹ ^ (S.m + 1) = S.Dd := by
      rw [inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx0), mul_one]
    have hblock : G.OmBlock S.β (S.m + 1) S.Ψ x⁻¹ (S.Dd * x ^ (S.m + 1)) = 0 := by
      obtain ⟨O, hO⟩ := hDg x⁻¹ _ (inv_ne_zero hx0) htδ hct
      obtain ⟨h1, h2, h3⟩ := hRel x⁻¹ _ (inv_ne_zero hx0) htδ hct
      have hv := hMB _ h1 h2 h3
      unfold VanAt at hv
      rw [← hO]
      exact hv O
    have hbound := hCst (Wq →L[ℂ] Wp) S.Ψ A K kk hA hk hDec x⁻¹ (S.Dd * x ^ (S.m + 1)) (inv_ne_zero hx0)
      (by rw [Set.mem_singleton_iff]; exact hct)
    unfold G.remainder at hbound
    rw [hblock, smul_zero, zero_sub, norm_neg, hct, germ_leading_term_root_sum S.β S.m S.Ψ x⁻¹ S.Dd S.z₀ S.z₀_pow,
      norm_smul, norm_inv x] at hbound
    have hsum : (∑ j : Fin R.card, G.psi S.β (((S.m : ℂ) + 2) * (e.symm j : ℂ) * x) •
        G.OmLong S.β (S.m + 1) S.Ψ (e.symm j : ℂ)) =
        ∑ z ∈ R, G.psi S.β (((S.m : ℂ) + 2) * z / x⁻¹) • G.OmLong S.β (S.m + 1) S.Ψ z := by
      rw [← Finset.sum_coe_sort R, ← Equiv.sum_comp e.symm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [div_inv_eq_mul]
    change ‖(_ : Wq →L[ℂ] Wp)‖ ≤ _
    rw [hsum, div_div,
      le_div_iff₀ (mul_pos (norm_pos_iff.mpr hc0) hxpos)]
    have hb2 := mul_le_mul_of_nonneg_right hbound hxpos.le
    rw [mul_assoc (Cst * K), inv_mul_cancel₀ hxpos.ne', mul_one] at hb2
    linarith [hb2]

theorem inner_averaging_input_from_slice : Formalism.FourierDecayAlt.OrbitalSlices.AvgInputJOfSlice := by
  intro hG hJ
  obtain ⟨C₁, C₂, hR⟩ := hG
  obtain ⟨CV₀, hCV⟩ := hJ C₁ C₂
  refine ⟨CV₀, ?_⟩
  intro CV hCV' k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ h1 h2 h3 h4
  obtain ⟨S, hS⟩ := hCV CV hCV' k r Wp Wq D A ε mm F' γ h1 h2 h3 h4
  exact averaging_datum_of_slice_point hR S hS

theorem top_averaging_input_from_slice : Formalism.FourierDecayAlt.OrbitalSlices.AvgInputTopOfSlice := by
  intro hG hT
  obtain ⟨C₁, C₂, hR⟩ := hG
  obtain ⟨CV₀, hCV⟩ := hT C₁ C₂
  refine ⟨CV₀, ?_⟩
  intro CV hCV' k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ h1 h2 h3 h4
  obtain ⟨S, hS⟩ := hCV CV hCV' k r Wp Wq D A ε mm F' γ h1 h2 h3 h4
  exact averaging_datum_of_slice_point hR S hS

theorem inner_averaging_input_of_slice_data (hJ : Formalism.FourierDecayAlt.OrbitalSlices.SliceInputJ) : Formalism.FourierDecayAlt.DensityAveraging.AvgInputJ :=
  inner_averaging_input_from_slice germ_rate hJ

theorem top_averaging_input_of_slice_data (hT : Formalism.FourierDecayAlt.OrbitalSlices.SliceInputTop) : Formalism.FourierDecayAlt.DensityAveraging.AvgInputTop :=
  top_averaging_input_from_slice germ_rate hT

theorem density_lemma_of_slice_data (hJ : Formalism.FourierDecayAlt.OrbitalSlices.SliceInputJ) (hT : Formalism.FourierDecayAlt.OrbitalSlices.SliceInputTop) :
    Formalism.FourierDecayAlt.C6.LemmaDens :=
  density_lemma_of_reductions
    (big_cell_density_of_parts (relevant_trivial_big_cell_of_parts stabilizer_split stabilizer_pairs))
    (inner_density_of_averaging (inner_averaging_input_of_slice_data hJ) averaging_vanishes)
    (top_density_of_averaging (top_averaging_input_of_slice_data hT) averaging_vanishes)

def slicePointInhabited {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) : Formalism.FourierDecayAlt.OrbitalSlices.SlicePt D F' γ where
  m := 0
  β := 1
  β_ne := one_ne_zero
  Dd := -1
  Dd_ne := by norm_num
  z₀ := 1
  z₀_pow := by norm_num
  Ψ := fun _ => 0
  pt := fun _ _ => γ
  δ := 1
  δ_pos := one_pos

end Formalism.FourierDecayAlt.P
