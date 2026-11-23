import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CyclicKummerNormFixedHilbert90Statement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.KummerGalois
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GaloisPlacesTransitive
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ValuationUnramifiedKummerOfCoprimeUnitStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitValuationEqOfAdm
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem hilbert90_sUnits_kummer : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → AdmP p F S → (∀ v, v ∉ S → v.valuation F δ = 1) → ∀ u : Eˣ, u ∈ sUnits E SE → ∏ i ∈ Finset.range p, σ^[i] (u : E) = 1 → ∃ y : Eˣ, y ∈ sUnits E SE ∧ (u : E) = σ y / y := by
  classical
  intro p F E _ _ _ _ _ ζ δ θ σ hq S SE hSE hadm hδ u hu hN
  obtain ⟨hfd, -, hgal, -, hgen, -⟩ := kummer_galois p F E ζ δ θ σ hq
  obtain ⟨y, hy0, hy⟩ := (GlobalTheory.T.cyclic_hilbert90_kummer_and_mem_kNorm_iff p F E ζ δ θ σ hq).2.2.2.2.1 (u : E) hN
  obtain ⟨hact, htrans⟩ := galois_places_transitive F E
  rw [mem_sUnits] at hu
  have hval : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ SE → w.valuation E (σ y) = w.valuation E y := by
    intro w hw
    have h1 := hu w hw
    rw [hy, map_div₀, div_eq_one_iff_eq (by simpa only [ne_eq, map_eq_zero] using hy0)] at h1
    exact h1
  have hpow : ∀ (k : ℕ) (w : HeightOneSpectrum (𝓞 E)), w ∉ SE →
      w.valuation E ((σ ^ k) y) = w.valuation E y := by
    intro k w hw
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨w', hw', hv'⟩ := hact (σ ^ k) w
      have hw'' : w' ∉ SE := fun h => hw ((hSE w).2 (hw' ▸ (hSE w').1 h))
      rw [pow_succ, AlgEquiv.mul_apply, ← hv', hval w' hw'', hv', ih]
  have hall : ∀ (τ : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E)), w ∉ SE →
      w.valuation E (τ y) = w.valuation E y := by
    intro τ w hw
    obtain ⟨k, rfl⟩ := mem_powers_iff_mem_zpowers.2 (hgen τ)
    exact hpow k w hw
  choose up hup using (places_over F E).2.1
  obtain ⟨T, -, hT⟩ := exists_superset_mem_sUnits E {Units.mk0 y hy0} ∅
  have hT' := (mem_sUnits E T _).1 (hT T subset_rfl _ (Finset.mem_singleton_self _))
  obtain ⟨a, ha⟩ := exists_unit_valuation_eq_of_adm F S (T.image fun w => w.under (𝓞 F))
    (fun v => -WithZero.log ((up v).valuation E y)) hadm.1 (by
      intro v hv
      have : up v ∉ T := fun h => hv (Finset.mem_image.2 ⟨_, h, hup v⟩)
      have h2 : (up v).valuation E y = 1 := hT' _ this
      simp [h2])
  have ha0 : algebraMap F E (a : F) ≠ 0 := by simp
  refine ⟨Units.mk0 (algebraMap F E a * y) (mul_ne_zero ha0 hy0), ?_, ?_⟩
  · rw [mem_sUnits]
    intro w hw
    have hv : w.under (𝓞 F) ∉ S := fun h => hw ((hSE w).2 h)
    have h3 : (up (w.under (𝓞 F))).valuation E y = w.valuation E y := by
      obtain ⟨τ, hτ⟩ := htrans w (up (w.under (𝓞 F))) (hup _)
      rw [hτ, hall τ w hw]
    have h4 : w.valuation E y ≠ 0 := by simpa only [ne_eq, map_eq_zero] using hy0
    rw [Units.val_mk0, map_mul,
      GlobalTheory.T.valuation_unramified_kummer_of_coprime_unit p F E ζ δ θ σ hq w (hadm.2 _ hv) (hδ _ hv), ha _ hv]
    simp only [h3]
    rw [WithZero.exp_neg, WithZero.exp_log h4, inv_mul_cancel₀ h4]
  · rw [Units.val_mk0, map_mul, AlgEquiv.commutes, hy, mul_div_mul_left _ _ ha0]

end GlobalTheory.CNorm
