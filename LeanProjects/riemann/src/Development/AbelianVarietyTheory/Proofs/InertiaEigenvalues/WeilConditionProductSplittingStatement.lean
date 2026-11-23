import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilConditionProductSplitting
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitting
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_condition_product_splitting : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L), IsSplitting A A₁ A₂ eK eL → WeilAt A₁ → WeilAt A₂ → WeilAt A := by
  first | exact @GlobalTheory.JR.WeilProd.weilAt_prod | exact GlobalTheory.JR.WeilProd.weilAt_prod | (intros; apply GlobalTheory.JR.WeilProd.weilAt_prod <;> assumption)
