import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Development

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol MeasureTheory NumberField IsDedekindDomain

def RightK : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) (μG : Measure (HA (Fv F v) σ J)),
    StdHyp σ J ψ → IsSDLoc σ J v Λ → UnramAt (E := E) v → etaV (E := E) v = 1 →
    LocMassOrdW.IsLatLoc v Λ → μG.IsHaarMeasure →
    ∀ κ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, ∀ A : Set (HA (Fv F v) σ J), MeasurableSet A →
      μG ((fun c => c * κ) ⁻¹' A) = μG A

end PI.LocMassTypW
