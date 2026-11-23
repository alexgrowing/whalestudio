import Mathlib
import Formalism.PeriodIntegrals.OmFibreUniq

noncomputable section

namespace PI.OmFibreUniq.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq
open scoped TensorProduct Classical

def SdEx : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (a : ℕ), StdHyp σ J ψ →
    (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧
      (∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν)

def FibEx : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (v : HeightOneSpectrum (𝓞 F)) (a : ℕ), IsCMExt F E σ → IsHermND σ J →
    ∀ (μ : Measure (TupV (E := E) v n a)) (ν : Measure (HermR (Fv F v) σ a)),
      μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
      ∃ fib, IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val (IndepV (E := E) (n := n) v a) ν
        Set.univ fib

def FibUniq : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (v : HeightOneSpectrum (𝓞 F)) (a : ℕ)
    (μ : Measure (TupV (E := E) v n a)) (ν : Measure (HermR (Fv F v) σ a)),
      ν.IsAddHaarMeasure → ∀ fib fib',
      IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val (IndepV (E := E) (n := n) v a) ν
        Set.univ fib →
      IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val (IndepV (E := E) (n := n) v a) ν
        Set.univ fib' → fib = fib'

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (a : ℕ)

theorem dX_haar (h : ∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) :
    (dX σ J ψ v a).IsAddHaarMeasure := by
  unfold dX
  rw [dif_pos h]
  exact h.choose_spec.1

theorem dT_haar (h : ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν) :
    (dT σ ψ v a).IsAddHaarMeasure := by
  unfold dT
  rw [dif_pos h]
  exact h.choose_spec.1

theorem omUnique_of (h0 : SdEx) (h1 : FibEx) (h4 : FibUniq) : OmUnique σ J ψ v a := by
  intro hS
  obtain ⟨hX, hT⟩ := h0 σ J ψ v a hS
  exact ⟨h1 σ J v a hS.1 hS.2.1 _ _ (dX_haar σ J ψ v a hX) (dT_haar σ ψ v a hT),
    fun fib fib' h h' => h4 σ J v a _ _ (dT_haar σ ψ v a hT) fib fib' h h'⟩

end

end PI.OmFibreUniq.W
