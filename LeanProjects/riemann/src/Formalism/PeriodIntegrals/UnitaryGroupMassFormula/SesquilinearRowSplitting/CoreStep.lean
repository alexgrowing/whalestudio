import Mathlib
import Formalism.PeriodIntegrals.SplitRow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoordStep

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.SRW

def CoreHyp {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {r : ℕ} {T : E}
    (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (F0 : FlagG S r T)
    (Λ : Submodule (𝓞 E) S.V) : Prop :=
  Submodule.IsLattice E Λ ∧ Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ ∧ F0.z ∈ Λ ∧
    (∀ c : E, c • F0.z ∈ Lsub Λ (⟨F0, F0.z⟩ : LFlag S r T) → ∃ o : 𝓞 E, (o : E) = c) ∧
    XLam Λ (⟨F0, F0.z⟩ : LFlag S r T) = Formalism.L2.SG.Saturated.latSpan aa F0.e ∧
    (∀ a, aa a ≠ 0) ∧ (∀ a, ∀ x ∈ aa a, star x ∈ aa a) ∧
    (∃ x : 𝓞 E, (x : E) + star (x : E) = 1)

def CoreStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (F0 : FlagG S r T)
    (Λ : Submodule (𝓞 E) S.V), CoreHyp S aa F0 Λ → Formalism.L2.SG.Saturated.IsSplitBy aa F0 Λ

def AaStep : Prop :=
  ∀ D : D7, ∀ a : Fin D.R.rS, Formalism.L2.SG.Saturated.aaS D a ≠ 0 ∧
    ∀ x ∈ Formalism.L2.SG.Saturated.aaS D a, (letI := D.host.cmStar; star x) ∈ Formalism.L2.SG.Saturated.aaS D a

def TrStep : Prop :=
  ∀ D : D7, ∃ x : 𝓞 D.host.E, (x : D.host.E) + (letI := D.host.cmStar; star (x : D.host.E)) = 1

end PI.SRW
