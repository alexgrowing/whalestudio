import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def firstGroup {F : Type*} [Field F] {n e : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin n) F) :
    MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) :=
  aeval (fun ij : Fin (e + 1) × Fin n =>
    Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
      (X ij.2) (fun i => C (X (i, ij.2))) ij.1) f

def ChartFirstGroupPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f →
      Prime (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) (firstGroup f))

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
