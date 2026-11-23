import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianIsometryBaseChange
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_isometry_base_change : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k k' : Type) [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k'] (ψ : k →ₐ[F] k') (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ), ∃ (x' : plusUnits P k') (φ' : (k' ⊗[F] Fld P) ≃ₗ[k' ⊗[F] E] (Fin n → k' ⊗[F] E)) (h' : IsIsom P k' J x'.1.1 φ'), x'.1.1 = Algebra.TensorProduct.map ψ (AlgHom.id F (Fld P)) x.1.1 ∧ gam h' = mapH σ J ψ (gam h) ∧ ∀ t, torEmb h' (mapH (star' P) (one₁ P) ψ t) = mapH σ J ψ (torEmb h t) := by
  first | exact @GlobalTheory.TrEll.BaseChg.exists_isom_baseChange | exact GlobalTheory.TrEll.BaseChg.exists_isom_baseChange | (intros; apply GlobalTheory.TrEll.BaseChg.exists_isom_baseChange <;> assumption)
