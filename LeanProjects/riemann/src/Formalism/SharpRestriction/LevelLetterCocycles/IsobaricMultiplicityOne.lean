import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE

noncomputable section

namespace Formalism.MainNotions.N.T2

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N

namespace SumRepresentations

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def StrongMultiplicityOneCuspidalSums : Prop :=
  (∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
    (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa')

def IsobaricMultiplicityOne : Prop :=
  (∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
    (∀ p ∈ Pa', 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
    (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa')

end SumRepresentations

end Formalism.MainNotions.N.T2

namespace Formalism.MainNotions.N.T2
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations in

theorem litGoodO : Formalism.MainNotions.N.LitGoodO := by
  intro l _ LL
  haveI : FiniteDimensional ℚ_[l] LL.1 := LL.2
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, LL.2, isModuleTopologyOfFiniteDimensional,
    inferInstance, ?_⟩
  have hr : Set.range (algebraMap (OL LL) LL.1) = ((OL LL).toSubring.toAddSubgroup : Set LL.1) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hr]
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0)
    (Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) ?_)
  intro x hx
  show x ∈ OL LL
  rw [Formalism.BasicNotions.Examples₂.LB.mem_OL]
  have : ‖x‖ < 1 := by simpa using hx
  exact le_of_lt this
end Formalism.MainNotions.N.T2
