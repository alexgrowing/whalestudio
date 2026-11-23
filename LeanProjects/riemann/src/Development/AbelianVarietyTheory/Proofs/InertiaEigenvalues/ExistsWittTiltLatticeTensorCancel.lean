import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL

theorem exists_cancel_tensor {R O A T : Type} [CommRing R] [CommRing O] [CommRing A] [Algebra R O]
    [Algebra R A] [AddCommGroup T] [Module O T] [Module R T] [IsScalarTower R O T] :
    ∃ κ : (A ⊗[R] T) ≃+ ((O ⊗[R] A) ⊗[O] T), ∀ (w : A) (t : T),
      κ (w ⊗ₜ[R] t) = ((1 : O) ⊗ₜ[R] w) ⊗ₜ[O] t := by
  haveI : SMulCommClass R O T := IsScalarTower.to_smulCommClass
  refine ⟨(TensorProduct.comm R A T).toAddEquiv.trans
    (((TensorProduct.AlgebraTensorModule.cancelBaseChange R O O T A).symm.toAddEquiv).trans
      (TensorProduct.comm O T (O ⊗[R] A)).toAddEquiv), fun w t => ?_⟩
  simp

theorem exists_cancel_tensor_compHom (R O A T : Type) [CommRing R] [CommRing O] [CommRing A] [Algebra R O]
    [Algebra R A] [AddCommGroup T] [Module O T] :
    letI : Module R T := Module.compHom T (algebraMap R O)
    ∃ κ : (A ⊗[R] T) ≃+ ((O ⊗[R] A) ⊗[O] T), ∀ (w : A) (t : T),
      κ (w ⊗ₜ[R] t) = ((1 : O) ⊗ₜ[R] w) ⊗ₜ[O] t := by
  letI : Module R T := Module.compHom T (algebraMap R O)
  haveI : IsScalarTower R O T := IsScalarTower.of_compHom R O T
  exact exists_cancel_tensor

theorem exists_kappa : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), letI := Formalism.MainNotions.LocalSituation.zlMod LL T; ∃ κ : (WCb l ⊗[ℤ_[l]] ↥T.L.T) ≃+ TW (RW LL) T, ∀ (w : WCb l) (t : ↥T.L.T), κ (w ⊗ₜ[ℤ_[l]] t) = TensorProduct.tmul ↥(OL LL) ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w : RW LL) t := by
  intro l _ K LL T
  exact exists_cancel_tensor_compHom ℤ_[l] ↥(OL LL) (WCb l) ↥T.L.T

end GlobalTheory.HWL
