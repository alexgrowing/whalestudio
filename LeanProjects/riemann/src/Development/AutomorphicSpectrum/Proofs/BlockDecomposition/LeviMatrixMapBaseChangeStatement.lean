import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMatrixMapBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_matrix_map_base_change : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} (A A' : Type) [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A'] (φ : A →ₐ[F] A') (M : Matrix (Fin n) (Fin n) (A ⊗[F] E)), leviMat σ J A' X Y (M.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) = (leviMat σ J A X Y M).map (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.leviMat_map | exact GlobalTheory.CompanionTheory.KFin.leviMat_map | (intros; apply GlobalTheory.CompanionTheory.KFin.leviMat_map <;> assumption)
