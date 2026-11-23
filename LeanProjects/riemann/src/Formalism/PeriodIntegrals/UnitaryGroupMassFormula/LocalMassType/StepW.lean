import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Development

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct Classical

def StepW : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E)) (T : F),
    StdHyp σ J ψ → P.IsStd σ J T → IsSDLoc σ J v Λ → UnramAt (E := E) v → etaV (E := E) v = 1 →
    IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P))) → LocMassOrdW.IsLatLoc v Λ →
    ∀ h : HA (Fv F v) σ J, IsPrim v Λ (locF v (h • ratTup (Fv F v) (F0 P))) →
      ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v,
        k • ratTup (F := F) (Fv F v) (F0 P) = h • ratTup (F := F) (Fv F v) (F0 P)

end PI.LocMassTypW
