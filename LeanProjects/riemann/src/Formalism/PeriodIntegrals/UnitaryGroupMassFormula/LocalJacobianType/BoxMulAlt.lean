import Mathlib
import Formalism.PeriodIntegrals.LocJacTyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Development

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def OTop : Prop :=
  IsCompact (OEv (E := E) v) ∧ IsOpen (OEv (E := E) v) ∧
  (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v ∧
  (∀ x ∈ OEv (E := E) v, ∀ y ∈ OEv (E := E) v, x * y ∈ OEv (E := E) v) ∧
  (∀ x ∈ OEv (E := E) v, ∀ y ∈ OEv (E := E) v, x + y ∈ OEv (E := E) v) ∧
  (∀ x ∈ OEv (E := E) v, -x ∈ OEv (E := E) v) ∧
  (∀ t ∈ v.adicCompletionIntegers F, ∀ x ∈ OEv (E := E) v, sc (E := E) v t * x ∈ OEv (E := E) v) ∧
  (∀ σ : E →ₐ[F] E, ∀ x ∈ OEv (E := E) v, sigR (Fv F v) σ x ∈ OEv (E := E) v)

def RTop : Prop :=
  LocallyCompactSpace (Fv F v ⊗[F] E) ∧ SecondCountableTopology (Fv F v ⊗[F] E) ∧
  T2Space (Fv F v ⊗[F] E) ∧ IsTopologicalRing (Fv F v ⊗[F] E)

def BoxMul : Prop :=
  ∀ (ι : Type) [Fintype ι] (μ : Measure (ι → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure]
    (y : ι → Fv F v ⊗[F] E), (∀ i, IsUnit (y i)) →
    (μ (Set.univ.pi fun i => {c | y i * c ∈ OEv (E := E) v})).toReal =
      (μ (Obox (E := E) v ι)).toReal * ∏ i, (absV v (Algebra.norm (Fv F v) (y i)))⁻¹

end PI.UnitaryGroupMassFormula.LocJacTyp
