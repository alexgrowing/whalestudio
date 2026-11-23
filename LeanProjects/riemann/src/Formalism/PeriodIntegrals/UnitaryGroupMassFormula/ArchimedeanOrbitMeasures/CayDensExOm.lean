import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExTop

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

section Lie

variable (P Q : ℕ)

theorem isClosed_lieU : IsClosed ((lieU P Q : Set (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))) := by
  change IsClosed {X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ | Xᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * X = 0}
  exact isClosed_eq
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).add
      (continuous_const.matrix_mul continuous_id)) continuous_const

instance : BorelSpace (lieU P Q) := ⟨rfl⟩

instance : LocallyCompactSpace (lieU P Q) := by
  haveI : LocallyCompactSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  exact (isClosed_lieU P Q).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance : SecondCountableTopology (lieU P Q) := by
  haveI : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  exact IsInducing.subtypeVal.secondCountableTopology

end Lie

end HcInf
