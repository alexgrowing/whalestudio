import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MeasCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.T2SpaceGeneralLinearGroup

noncomputable section

namespace PI.UnitaryGroupMassFormula.MeasWCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def SplitH : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (P : Frame E n r) (T : F),
    IsCMExt F E σ → IsHermND σ J → P.IsStd σ J T →
    ∃ e : (Hsub (Ainf F) σ J P × Hsub (Af F) σ J P) ≃ₜ* Hsub (AF F) σ J P,
      ∀ p, splitA σ J (e p : HA (AF F) σ J) = ((p.1 : HA (Ainf F) σ J), (p.2 : HA (Af F) σ J))

def SplitN : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (P : Frame E n r) (T : F),
    IsCMExt F E σ → IsHermND σ J → P.IsStd σ J T →
    ∃ e : (Nsub (Ainf F) σ J P × Nsub (Af F) σ J P) ≃ₜ* Nsub (AF F) σ J P,
      ∀ p, splitA σ J (e p : HA (AF F) σ J) = ((p.1 : HA (Ainf F) σ J), (p.2 : HA (Af F) σ J))

def ContSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsCMExt F E σ → Continuous (splitA σ J)

def SProd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (P : Frame E n r) (T : F),
    IsCMExt F E σ → IsHermND σ J → P.IsStd σ J T →
    ∀ (μNf : Measure (Nsub (Af F) σ J P)) (μHf : Measure (Hsub (Af F) σ J P)),
      μNf.IsHaarMeasure → μHf.IsHaarMeasure →
      ∃ μSf : Measure (Ssub (Af F) σ J P), μSf.IsHaarMeasure ∧
        amb μSf = ((amb μNf).prod (amb μHf)).map (fun p => p.1 * p.2)

end PI.UnitaryGroupMassFormula.MeasWCore
