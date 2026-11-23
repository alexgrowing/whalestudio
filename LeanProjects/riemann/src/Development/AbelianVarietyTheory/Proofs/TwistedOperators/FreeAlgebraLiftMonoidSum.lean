import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open scoped InnerProductSpace

namespace GlobalTheory

theorem freeAlgebra_lift_eq_sum_monomials {B : Type} [Ring B] [Algebra ℂ B] {X : Type} (f : X → B) (p : FreeAlgebra ℂ X) : FreeAlgebra.lift ℂ f p = Finsupp.sum (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).coeff fun (w : FreeMonoid X) (c : ℂ) => c • (w.toList.map f).prod := by
  set e := (FreeAlgebra.equivMonoidAlgebraFreeMonoid : FreeAlgebra ℂ X ≃ₐ[ℂ] MonoidAlgebra ℂ (FreeMonoid X))
  have he : ∀ x : X, e (FreeAlgebra.ι ℂ x) = MonoidAlgebra.of ℂ (FreeMonoid X) (FreeMonoid.of x) := by
    intro x
    simp [e, FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  have hF : ((FreeAlgebra.lift ℂ f).comp e.symm.toAlgHom) = MonoidAlgebra.lift ℂ B (FreeMonoid X) (FreeMonoid.lift f) := by
    rw [← (MonoidAlgebra.lift ℂ B (FreeMonoid X)).apply_symm_apply ((FreeAlgebra.lift ℂ f).comp e.symm.toAlgHom)]
    congr 1
    apply FreeMonoid.hom_eq
    intro x
    have hx : e.symm (MonoidAlgebra.of ℂ (FreeMonoid X) (FreeMonoid.of x)) = FreeAlgebra.ι ℂ x := by
      rw [← he x, e.symm_apply_apply]
    rw [MonoidAlgebra.of_apply] at hx
    rw [MonoidAlgebra.lift_symm_apply]
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.coe_algHom, hx, FreeAlgebra.lift_ι_apply, FreeMonoid.lift_eval_of]
  have := AlgHom.congr_fun hF (e p)
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply, MonoidAlgebra.lift_apply, FreeMonoid.lift_apply] at this
  exact this
end GlobalTheory
