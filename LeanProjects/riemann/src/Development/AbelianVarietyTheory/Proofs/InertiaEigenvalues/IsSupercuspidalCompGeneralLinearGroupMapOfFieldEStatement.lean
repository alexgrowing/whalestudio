import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalCompGeneralLinearGroupMapOfFieldE
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSupercuspidal_comp_generalLinearGroupMapOfFieldEquiv : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i.symm → ∀ {n : Type} [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V), GlobalTheory.SmGL.IsCuspidal π → GlobalTheory.SmGL.IsCuspidal (π.comp (Matrix.GeneralLinearGroup.map (n := n) i.symm.toRingHom)) := by
  first | exact @GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap | exact GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap | (intros; apply GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap <;> assumption)
