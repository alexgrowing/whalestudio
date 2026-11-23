import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NineTermExactIff

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

theorem map_mem_closedNormal {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] (Φ : A ≃ₜ* B) (X : Set A) (Y : Set B)
    (h : ∀ a ∈ X, Φ a ∈ Y) {a : A} (ha : a ∈ (Subgroup.normalClosure X).topologicalClosure) :
    Φ a ∈ (Subgroup.normalClosure Y).topologicalClosure := by
  let f : A →* B := (Φ : A ≃* B).toMonoidHom
  let K : Subgroup B := (Subgroup.normalClosure Y).topologicalClosure
  haveI : K.Normal := Subgroup.is_normal_topologicalClosure _
  haveI : (K.comap f).Normal := Subgroup.Normal.comap ‹_› f
  have hK : IsClosed (K : Set B) := Subgroup.isClosed_topologicalClosure _
  have hc : IsClosed ((K.comap f : Subgroup A) : Set A) := hK.preimage Φ.continuous
  have hle : Subgroup.normalClosure X ≤ K.comap f := by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (h x hx))
  exact Subgroup.topologicalClosure_minimal _ hle hc ha

def quotientIso {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] (Φ : A ≃ₜ* B)
    (H : Subgroup A) (K : Subgroup B) [H.Normal] [K.Normal] (h : ∀ a, a ∈ H ↔ Φ a ∈ K) :
    A ⧸ H ≃ₜ* B ⧸ K where
  toMulEquiv := QuotientGroup.congr H K (Φ : A ≃* B) (by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (h a).1 ha
    · intro hb
      exact ⟨Φ.symm b, (h _).2 (by simpa using hb), Φ.apply_symm_apply b⟩)
  continuous_toFun := by
    exact (QuotientGroup.isQuotientMap_mk H).continuous_iff.2
      (QuotientGroup.continuous_mk.comp Φ.continuous)
  continuous_invFun := by
    exact (QuotientGroup.isQuotientMap_mk K).continuous_iff.2
      (QuotientGroup.continuous_mk.comp Φ.symm.continuous)

theorem exists_gsIso : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ↔ IsPlaceOver A' (eV v)) → (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') → ∀ (T : Set (HeightOneSpectrum (𝓞 F))) (T' : Set (HeightOneSpectrum (𝓞 F'))), (∀ v, v ∈ T ↔ eV v ∈ T') → ∃ Ψ : GS Ω T ≃ₜ* GS Ω' T', ∀ σ : G F Ω, Ψ (toGS Ω T σ) = toGS Ω' T' (Φ σ) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E _ Φ _ eV hP hI T T' hT
  have hfwd : ∀ σ, σ ∈ NS Ω T → Φ σ ∈ NS Ω' T' := by
    intro σ hσ
    refine map_mem_closedNormal Φ _ _ ?_ hσ
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ ⊢
    obtain ⟨v, hv, A, hA, hτ⟩ := hτ
    let A' : ValuationSubring Ω' := A.comap (E.symm : Ω' →+* Ω)
    have hAA : ∀ x, E x ∈ A' ↔ x ∈ A := by
      intro x
      show E.symm (E x) ∈ A ↔ x ∈ A
      simp
    exact ⟨eV v, fun h => hv ((hT v).2 h), A', (hP A A' hAA v).1 hA, (hI A A' hAA τ).1 hτ⟩
  have hbwd : ∀ σ', σ' ∈ NS Ω' T' → Φ.symm σ' ∈ NS Ω T := by
    intro σ' hσ'
    refine map_mem_closedNormal Φ.symm _ _ ?_ hσ'
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ ⊢
    obtain ⟨v', hv', A', hA', hτ⟩ := hτ
    let A : ValuationSubring Ω := A'.comap (E : Ω →+* Ω')
    have hAA : ∀ x, E x ∈ A' ↔ x ∈ A := fun x => Iff.rfl
    refine ⟨eV.symm v', fun h => hv' ?_, A, ?_, ?_⟩
    · simpa using (hT _).1 h
    · refine (hP A A' hAA _).2 ?_
      simpa using hA'
    · refine (hI A A' hAA _).2 ?_
      simpa using hτ
  have hiff : ∀ σ, σ ∈ NS Ω T ↔ Φ σ ∈ NS Ω' T' := fun σ =>
    ⟨hfwd σ, fun h => by simpa using hbwd _ h⟩
  exact ⟨quotientIso Φ (NS Ω T) (NS Ω' T') hiff, fun σ => rfl⟩

end GlobalTheory.CompanionTheory.PTIso
