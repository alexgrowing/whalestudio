import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTwoPlacesOverOfIsSquareLocalStatement

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem two_mul_card_le_card_over : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → 2 * S.card ≤ SE.card + tFin F δ S := by
  intro F E _ _ _ _ _ δ θ σ hq S SE hSE
  classical
  have h1 : SE.card = ∑ v ∈ S, (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun w hw => (hSE w).1 hw)
  have h2 : tFin F δ S
      = ∑ v ∈ S, if ¬ IsSquare (algebraMap F (v.adicCompletion F) δ) then 1 else 0 := by
    rw [← Finset.card_filter, tFin, ← Set.ncard_coe_finset]
    congr 1
    ext v
    simp
  rw [h1, h2, ← Finset.sum_add_distrib, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum (fun v hv => ?_)
  by_cases hs : IsSquare (algebraMap F (v.adicCompletion F) δ)
  · obtain ⟨w, w', hne, hw, hw'⟩ := GlobalTheory.T.exists_two_places_over_of_isSquare_local F E δ θ σ hq v hs
    have : 1 < (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
      Finset.one_lt_card.2 ⟨w, Finset.mem_filter.2 ⟨(hSE w).2 (hw ▸ hv), hw⟩,
        w', Finset.mem_filter.2 ⟨(hSE w').2 (hw' ▸ hv), hw'⟩, hne⟩
    omega
  · obtain ⟨w, hw⟩ := (places_over F E).2.1 v
    have : 0 < (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
      Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨(hSE w).2 (hw ▸ hv), hw⟩⟩
    rw [if_pos hs]
    omega

end GlobalTheory.QNorm
