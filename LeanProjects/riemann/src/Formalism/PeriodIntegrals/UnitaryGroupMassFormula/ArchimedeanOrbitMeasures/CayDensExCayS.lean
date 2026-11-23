import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExTop

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

def cayS {P Q : ℕ} (U : Set (lieU P Q)) : Set (UpqT P Q) :=
  {g | ∃ X ∈ U, UpqT.mat g *
    ((1 + 1) - ((X : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) =
      (1 + 1) + ((X : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)}

def CayleyLoc : Prop :=
  ∀ (P Q : ℕ) (m : Measure (UpqT P Q)), m.IsHaarMeasure → ∀ c : ℝ≥0∞, c ≠ 0 → c ≠ ⊤ →
  ∀ lam : Measure (lieU P Q), IsOmegaLeb lam →
    Tendsto (fun r : ℝ => m {g | ∃ X ∈ ballU P Q r, UpqT.mat g =
      NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} /
      lam (ballU P Q r)) (𝓝[>] 0) (𝓝 c) →
  ∀ ε : ℝ≥0, 0 < ε → ∃ V ∈ 𝓝 (0 : lieU P Q), MeasurableSet V ∧ MeasurableSet (cayS V) ∧
    ∃ ι : UpqT P Q → lieU P Q, Measurable ι ∧
      (∀ (g : UpqT P Q) (X : lieU P Q), X ∈ V →
        (UpqT.mat g * ((1 + 1) - ((X : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) =
          (1 + 1) + ((X : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) ↔
          g ∈ cayS V ∧ ι g = X)) ∧
      ∃ f : lieU P Q → ℝ≥0∞, Measurable f ∧ (∀ X ∈ V, f X ≤ (1 + ε) * c ∧ c ≤ (1 + ε) * f X) ∧
        (m.restrict (cayS V)).map ι = (lam.restrict V).withDensity f

end HcInf
