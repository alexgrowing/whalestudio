import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.StepW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.ColumnAdditionFixesTranspose
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.WCoreDef

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain Matrix
open scoped TensorProduct

def SplitR : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)),
    StdHyp σ J ψ → UnramAt (E := E) v → etaV (E := E) v = 1 →
    ∃ (e : Fv F v ⊗[F] E) (π₁ π₂ : Fv F v ⊗[F] E →+* Fv F v),
      e * e = e ∧ sigR (Fv F v) σ e = 1 - e ∧
      (∀ x, x * e = sc (E := E) v (π₁ x) * e) ∧ (∀ x, x * (1 - e) = sc (E := E) v (π₂ x) * (1 - e)) ∧
      π₁ e = 1 ∧ π₂ e = 0 ∧ (∀ c : Fv F v, π₁ (sc (E := E) v c) = c ∧ π₂ (sc (E := E) v c) = c) ∧
      (∀ x, π₂ (sigR (Fv F v) σ x) = π₁ x) ∧ (∀ x, π₁ (sigR (Fv F v) σ x) = π₂ x) ∧
      (∀ x, x ∈ OEv (E := E) v ↔
        π₁ x ∈ v.adicCompletionIntegers F ∧ π₂ x ∈ v.adicCompletionIntegers F)

def LatStd : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)),
    StdHyp σ J ψ → IsSDLoc σ J v Λ → UnramAt (E := E) v → etaV (E := E) v = 1 →
    LocMassOrdW.IsLatLoc v Λ →
    ∃ Q : GL (Fin n) (Fv F v ⊗[F] E),
      (∀ y, y ∈ latLoc (E := E) v Λ ↔
        ∃ x : Fin n → Fv F v ⊗[F] E, (∀ i, x i ∈ OEv (E := E) v) ∧
          y = (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x) ∧
      ∀ x y : Fin n → Fv F v ⊗[F] E,
        hR (Fv F v) σ J ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x)
          ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y) = ∑ i, sigR (Fv F v) σ (x i) * y i

def SatSplit : Prop :=
  ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n m : ℕ)
    (A : Matrix (Fin n) (Fin m) (v.adicCompletionIntegers F)),
    (∀ t : Fin m → v.adicCompletion F,
      (∀ i, (A.map (fun a => (a : v.adicCompletion F)) *ᵥ t) i ∈ v.adicCompletionIntegers F) →
      ∀ j, t j ∈ v.adicCompletionIntegers F) →
    ∃ L : Matrix (Fin m) (Fin n) (v.adicCompletionIntegers F), L * A = 1

end PI.LocMassTypW
