import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryProductReflections
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_product_reflections : ∀ {R : Type} [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → NormOneGen c → ∀ {M : ℕ} (Jm : Matrix (Fin M) (Fin M) R), (∀ i j, c (Jm j i) = Jm i j) → ∀ e : Fin M → Fin M → R, (∀ i j, i ≠ j → Formalism.UG.hform c Jm (e i) (e j) = 0) → (∀ i, IsUnit (Formalism.UG.hform c Jm (e i) (e i))) → IsUnit (Matrix.of e).det → ∀ x : GL (Fin M) R, x ∈ Formalism.UG.UJ c Jm → ∃ l : List (GL (Fin M) R), (∀ y ∈ l, y ∈ Formalism.UG.UJ c Jm ∧ IsQR c Jm (y : Matrix (Fin M) (Fin M) R)) ∧ l.prod = x := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.ReflList.exists_qr_list | exact GlobalTheory.CompanionTheory.SaGen.ReflList.exists_qr_list | (intros; apply GlobalTheory.CompanionTheory.SaGen.ReflList.exists_qr_list <;> assumption)
