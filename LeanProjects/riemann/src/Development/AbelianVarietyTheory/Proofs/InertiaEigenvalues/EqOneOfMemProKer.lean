import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Small2
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.TameRead

open GlobalTheory.TameQuot

theorem eq_one_of_mem_proKer {I M : Type} [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
    [CompactSpace I] [AddCommGroup M] {l : ℕ} [Fact l.Prime] {k : ℕ}
    (hM : ∀ m : M, (l ^ k) • m = 0) (θ : I →* Multiplicative M)
    (ho : IsOpen (θ.ker : Set I)) {σ : I} (hσ : σ ∈ proKer l I) : θ σ = 1 := by
  refine mem_proKer.1 hσ θ.ker inferInstance ho ?_
  have := Subgroup.quotient_finite_of_isOpen _ ho
  refine IsPGroup.iff_card.1 fun x => ⟨k, ?_⟩
  obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow]
  exact hM (θ τ).toAdd

theorem exists_gen_read : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∃ γ ∈ Ine (F := F) A, ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R (G F Ω) M) (k : ℕ), (∀ m : M, (l ^ k) • m = 0) → normV v ≡ 1 [MOD l ^ k] → (∀ σ ∈ Ine (F := F) A, ∀ m, rho σ m = m) → ∀ z : Z1 rho, (z.1 γ = 0 → ∀ σ ∈ Ine (F := F) A, z.1 σ = 0) ∧ ∀ φ : G F Ω, IsFrob A (normV v) φ → rho φ (z.1 γ) = z.1 γ := by
  intro hT F Ω _ _ _ _ _ l _ A v hA hl
  obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hrel⟩ := hT F Ω l A v hA hl
  refine ⟨γ, hγ.1, ?_⟩
  intro R _ M _ _ _ _ rho k hM hq hI z
  have : CompactSpace (Ine (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  let θ : Ine (F := F) A →* Multiplicative M :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (z.1 g)) fun g h => by
      have := z.2.2 (g : G F Ω) h
      rw [hI _ g.2] at this
      exact congrArg Multiplicative.ofAdd this
  have ho : IsOpen (θ.ker : Set (Ine (F := F) A)) :=
    (isOpen_discrete {0}).preimage (z.2.1.comp continuous_subtype_val)
  have hJ : ∀ σ ∈ ineKer F A l, z.1 σ = 0 := fun σ hσ =>
    eq_one_of_mem_proKer hM θ ho (σ := ⟨σ, ineKer_le_Ine A l hσ⟩) (coe_mem_ineKer.1 hσ)
  refine ⟨fun h0 σ hσ => ?_, fun φ hφ => ?_⟩
  · have hc : IsClosed ((θ.ker.map (Ine (F := F) A).subtype : Subgroup (G F Ω)) : Set (G F Ω)) :=
      (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ (θ.ker.isClosed_of_isOpen ho)
    have h1 : Subgroup.zpowers γ ⊔ ineKer F A l ≤ θ.ker.map (Ine (F := F) A).subtype :=
      sup_le (Subgroup.zpowers_le.2 ⟨⟨γ, hγ.1⟩, h0, rfl⟩) fun τ hτ =>
        ⟨⟨τ, ineKer_le_Ine A l hτ⟩, hJ τ hτ, rfl⟩
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.topologicalClosure_minimal _ h1 hc (hγ.2 hσ)
    exact hτ
  · have hc : φ * γ * φ⁻¹ ∈ Ine (F := F) A := conj_mem_Ine hφ.1 hγ.1
    have h1 := hJ _ (hrel ⟨φ, hφ.1⟩ ⟨γ, Ine_le_Dec A hγ.1⟩ hφ hγ).2.1
    have h2 : θ (((⟨γ, hγ.1⟩ : Ine (F := F) A) ^ normV v)⁻¹ * ⟨_, hc⟩) = 1 := h1
    rw [map_mul, map_inv, map_pow, inv_mul_eq_one] at h2
    have h3 : normV v • z.1 γ = z.1 (φ * γ * φ⁻¹) := congrArg Multiplicative.toAdd h2
    have h4 : normV v • z.1 γ = z.1 γ := by
      rw [← Nat.mod_add_div (normV v) (l ^ k), add_smul, mul_smul, hM, add_zero, hq]
      conv_rhs => rw [← one_smul ℕ (z.1 γ), ← Nat.mod_add_div 1 (l ^ k), add_smul, mul_smul, hM,
        add_zero]
    have h5 := z.2.2 (φ * γ * φ⁻¹) φ
    rw [hI _ hc, inv_mul_cancel_right, z.2.2 φ γ, ← h3, h4, add_comm] at h5
    exact add_right_cancel h5

end GlobalTheory.TameRead
