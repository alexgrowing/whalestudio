import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallLetterTypeFunctional
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_forall_letterType_functional : ∀ {L U D F k : Type} [Field L] [Field U] [AddCommGroup D] [Module L D] (m : U →+* Module.End L D) [Field F] [Field k] [Algebra k L] [Algebra k U] [Algebra k F] [Algebra U F] [IsScalarTower k U F] [IsAlgClosed F] [FiniteDimensional k L] [Algebra.IsSeparable k L] [Module U D] [FiniteDimensional U D], (∀ (c : U) (x : D), c • x = m c x) → (∀ (c : k) (x : D), m (algebraMap k U c) x = algebraMap k L c • x) → ∀ x : D, (∀ s : L →ₐ[k] F, ∀ f ∈ GlobalTheory.Pst.LetterDim.letterHom m (s : L →+* F) (algebraMap U F), f x = 0) → x = 0 := by
  first | exact @GlobalTheory.LetterSep.eq_zero_of_forall_letterHom | exact GlobalTheory.LetterSep.eq_zero_of_forall_letterHom | (intros; apply GlobalTheory.LetterSep.eq_zero_of_forall_letterHom <;> assumption)
