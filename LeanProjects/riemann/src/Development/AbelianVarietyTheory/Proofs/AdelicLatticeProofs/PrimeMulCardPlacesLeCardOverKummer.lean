import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.KummerGalois
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoPlacesOfEmbeddings
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NcardPlacesOverEqOfPrimeDegree
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem prime_mul_card_le_card_over : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → p * S.card ≤ SE.card + (p - 1) * tNon p F δ S := by
  intro p F E _ _ _ _ _ ζ δ θ σ hq S SE hSE
  classical
  have hp := hq.prime
  obtain ⟨-, hrk, hgal, -, -, -, hemb⟩ := kummer_galois p F E ζ δ θ σ hq
  have h1 : SE.card = ∑ v ∈ S, (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun w hw => (hSE w).1 hw)
  have h2 : tNon p F δ S
      = ∑ v ∈ S, if (∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ)
        then 1 else 0 := by
    rw [← Finset.card_filter, tNon, ← Set.ncard_coe_finset]
    congr 1
    ext v
    simp
  rw [h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib, mul_comm, ← smul_eq_mul,
    ← Finset.sum_const]
  refine Finset.sum_le_sum (fun v hv => ?_)
  by_cases hs : ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ
  · obtain ⟨w, hw⟩ := (places_over F E).2.1 v
    have : 0 < (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
      Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨(hSE w).2 (hw ▸ hv), hw⟩⟩
    rw [if_pos hs]
    omega
  · rw [if_neg hs]
    push Not at hs
    obtain ⟨r, hr⟩ := hs
    have hδ : δ ≠ 0 := fun h0 => hq.nonpow 0 (by rw [h0, zero_pow hp.ne_zero])
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp.ne_zero, eq_comm, map_eq_zero] at hr
      exact hδ hr
    obtain ⟨ψ, hψ⟩ := hemb (v.adicCompletion F) r hr
    obtain ⟨ψ', hψ'⟩ := hemb (v.adicCompletion F) (algebraMap F (v.adicCompletion F) ζ * r)
      (by rw [mul_pow, ← map_pow, hq.root.pow_eq_one, map_one, one_mul, hr])
    have hne : ψ ≠ ψ' := by
      intro h
      rw [← h, hψ, eq_comm, mul_eq_right₀ hr0,
        ← map_one (algebraMap F (v.adicCompletion F))] at hψ'
      exact hq.root.ne_one hp.one_lt ((algebraMap F (v.adicCompletion F)).injective hψ')
    obtain ⟨w, w', hww, hw, hw'⟩ := two_places_of_embeddings F E v ψ ψ' hne
    have h3 := ncard_places_over_eq_of_prime_degree p F E hp hrk v w w' hww hw hw'
    have h4 : (SE.filter (fun w => w.under (𝓞 F) = v)).card = p := by
      rw [← h3, ← Set.ncard_coe_finset]
      congr 1
      ext u
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨fun h => h.2, fun h => ⟨(hSE u).2 (h ▸ hv), h⟩⟩
    omega

end GlobalTheory.CNorm
