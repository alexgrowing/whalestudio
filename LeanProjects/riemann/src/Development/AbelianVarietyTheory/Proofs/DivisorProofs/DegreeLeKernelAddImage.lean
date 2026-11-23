import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrameMapOfAppendStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexAppendLeMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDetGramAppendLeStatement

open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

namespace GlobalTheory

theorem deg_le_deg_ker_add_deg_map_add : ∀ (K : Type) [Field K] [NumberField K] (m m' : ℕ) (h : HermFam K (Fin m → K)) (h' : HermFam K (Fin m' → K)) (q : (Fin m → K) →ₗ[K] (Fin m' → K)) (C : ℝ), 0 < C → ∀ W : Submodule (𝓞 K) (Fin m → K), W.FG → (∀ (σ : K →+* ℂ) (n : ℕ) (v : Fin n → Fin m → K), (∀ i, v i ∈ W) → ((C : ℂ) • h.gram σ v - h'.gram σ (q ∘ v)).PosSemidef) → deg h W ≤ deg h (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)) + deg h' (W.map (q.restrictScalars (𝓞 K))) + (latRank K (W.map (q.restrictScalars (𝓞 K))) : ℝ) / 2 * Real.log C := by
  intro K _ _ m m' h h' q C hC W hW hPSD
  classical
  have hWK : (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)).FG := by
    haveI : IsNoetherian (𝓞 K) W := isNoetherian_of_fg_of_noetherian W hW
    have h2 := (IsNoetherian.noetherian ((W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)).comap W.subtype)).map W.subtype
    rwa [Submodule.map_comap_eq_of_le (by simpa using inf_le_left)] at h2
  obtain ⟨a, ha⟩ := exists_isFrame (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)) hWK
  obtain ⟨w, hw⟩ := exists_isFrame W hW
  obtain ⟨t, b, -, hu⟩ := HadamardFrameExtension.exists_append_frame a ha.2.1 (fun i => (ha.1 i).1) w hw
  have hqb := GlobalTheory.T.isFrame_map_of_append K m m' q W _ t a b ha hu
  have hqW : (W.map (q.restrictScalars (𝓞 K))).FG := hW.map _
  have ht := hqb.card_eq
  have hI := GlobalTheory.T.relIndex_append_le_mul K m m' q W hW _ t a b ha hu
  have hIu := hu.relIndex_ne_zero hW
  have hIa := ha.relIndex_ne_zero hWK
  have hIb := hqb.relIndex_ne_zero hqW
  have hdet : ∀ σ : K →+* ℂ, Real.log (h.gram σ a).det.re + Real.log (h'.gram σ (q ∘ b)).det.re ≤
      Real.log (h.gram σ (Fin.append a b)).det.re + t * Real.log C := fun σ =>
    GlobalTheory.T.log_det_gram_append_le K m m' h h' q C hC σ _ t a b hu.2.1 hqb.2.1
      (fun i => by have := (ha.1 i).2; simpa using this) (hPSD σ _ _ hu.1)
  have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) => hdet σ)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card, nsmul_eq_mul] at hsum
  have hlog : Real.log ((Submodule.span (𝓞 K) (Set.range (Fin.append a b))).toAddSubgroup.relIndex W.toAddSubgroup : ℝ) ≤
      Real.log ((Submodule.span (𝓞 K) (Set.range a)).toAddSubgroup.relIndex (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)).toAddSubgroup : ℝ) +
      Real.log ((Submodule.span (𝓞 K) (Set.range (q ∘ b))).toAddSubgroup.relIndex (W.map (q.restrictScalars (𝓞 K))).toAddSubgroup : ℝ) := by
    rw [← Real.log_mul (by exact_mod_cast hIa) (by exact_mod_cast hIb)]
    exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hIu) (by exact_mod_cast hI)
  rw [arakelovDegree_eq_degreeOfFamily h hW hu, arakelovDegree_eq_degreeOfFamily h hWK ha, arakelovDegree_eq_degreeOfFamily h' hqW hqb, ← ht]
  unfold degreeOfFamily
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  rw [← add_div, ← sub_nonneg]
  have key : 0 ≤ (Real.log ((Submodule.span (𝓞 K) (Set.range a)).toAddSubgroup.relIndex (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)).toAddSubgroup : ℝ) - 1 / 2 * ∑ σ : K →+* ℂ, Real.log (h.gram σ a).det.re +
      (Real.log ((Submodule.span (𝓞 K) (Set.range (q ∘ b))).toAddSubgroup.relIndex (W.map (q.restrictScalars (𝓞 K))).toAddSubgroup : ℝ) - 1 / 2 * ∑ σ : K →+* ℂ, Real.log (h'.gram σ (q ∘ b)).det.re) +
      (t : ℝ) / 2 * Real.log C * Module.finrank ℚ K) -
      (Real.log ((Submodule.span (𝓞 K) (Set.range (Fin.append a b))).toAddSubgroup.relIndex W.toAddSubgroup : ℝ) - 1 / 2 * ∑ σ : K →+* ℂ, Real.log (h.gram σ (Fin.append a b)).det.re) := by
    nlinarith
  have e : ∀ A B X : ℝ, A / Module.finrank ℚ K + (t : ℝ) / 2 * Real.log C - B / Module.finrank ℚ K =
      (A + (t : ℝ) / 2 * Real.log C * Module.finrank ℚ K - B) / Module.finrank ℚ K := by
    intros; field_simp
  rw [e _ _ 0]
  exact div_nonneg key hd.le

end GlobalTheory
