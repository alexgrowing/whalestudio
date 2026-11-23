import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct

namespace GlobalTheory.ThKUTr

theorem cmConj_ne_id {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ¬ ∀ x, σ x = x := by
  intro hx
  obtain ⟨_, hE, _, hτ⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := hτ τ x
  rw [hx] at this
  simpa using this.symm

theorem cmConj_fixed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (a : E) : σ a = a ↔ a ∈ (algebraMap F E).range := by
  constructor
  · intro ha
    have hs : IsSimpleOrder (Subalgebra F E) :=
      Subalgebra.isSimpleOrder_of_finrank_prime F E (by rw [h.2.2.1]; exact Nat.prime_two)
    have ha' : a ∈ AlgHom.equalizer σ (AlgHom.id F E) := ha
    rcases hs.eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h0 | h0
    · rw [h0, Algebra.mem_bot] at ha'
      exact ha'
    · exfalso
      refine cmConj_ne_id h fun x => ?_
      have : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := h0 ▸ Algebra.mem_top
      exact this
  · rintro ⟨b, rfl⟩
    exact σ.commutes b

noncomputable def intRestr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) : 𝓞 E →ₐ[𝓞 F] 𝓞 E :=
  { RingOfIntegers.mapRingHom (σ : E →+* E) with
    commutes' := fun r => by
      apply Subtype.ext
      exact σ.commutes (r : F) }

theorem intRestr_coe {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (x : 𝓞 E) :
    algebraMap (𝓞 E) E (intRestr σ x) = σ (algebraMap (𝓞 E) E x) := rfl

theorem exists_sub_notMem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hne : ¬ ∀ x, σ x = x) (hU : Algebra.Unramified (𝓞 F) (𝓞 E))
    (P : Ideal (𝓞 E)) (hP : P ≠ ⊤) : ∃ θ : 𝓞 E, θ - intRestr σ θ ∉ P := by
  by_contra hc
  push Not at hc
  have hF : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := hU.formallyUnramified
  have he : AlgHom.id (𝓞 F) (𝓞 E) = intRestr σ :=
    Algebra.FormallyUnramified.ext_of_iInf P (Ideal.iInf_pow_eq_bot_of_isDomain P hP)
      fun x => Ideal.Quotient.eq.2 (hc x)
  have h1 : ∀ y : 𝓞 E, σ (algebraMap (𝓞 E) E y) = algebraMap (𝓞 E) E y := fun y => by
    rw [← intRestr_coe, ← he]; rfl
  apply hne
  intro x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  rw [map_div₀, h1, h1]

theorem cmData_starOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → @Formalism.BasicNotions.CMData F E _ _ _ _ (GlobalTheory.ThKUTr.starOf σ hσ) _ := by
  intro F E _ _ _ _ _ σ hσ h hU
  letI := GlobalTheory.ThKUTr.starOf σ hσ
  refine ⟨⟨h.2.1, fun φ a => h.2.2.2 φ a, fun P hP => ?_⟩, h.1, h.2.2.1, fun a => cmConj_fixed h a⟩
  obtain ⟨θ, hθ⟩ := exists_sub_notMem σ (cmConj_ne_id h) hU P hP.ne_top
  exact ⟨θ, intRestr σ θ, rfl, hθ⟩

end GlobalTheory.ThKUTr
