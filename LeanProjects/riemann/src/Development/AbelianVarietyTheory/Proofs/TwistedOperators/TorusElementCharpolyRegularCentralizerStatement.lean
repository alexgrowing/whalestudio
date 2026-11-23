import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusElementCharpolyRegularCentralizer
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusElement_charpoly_regular_centralizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : Type) [CommRing k] [Algebra F k], ∀ (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ), (GlobalTheory.AdelicU.matHom k σ J (gam h)).1.charpoly = P.1.map (inclR k) ∧ IsRegSS (GlobalTheory.AdelicU.matHom k σ J (gam h)).1 ∧ Function.Injective (torEmb h) ∧ cent (gam h) = (torEmb h).range := by
  first | exact @GlobalTheory.TrEll.gam_charpoly_regular_cent | exact GlobalTheory.TrEll.gam_charpoly_regular_cent | (intros; apply GlobalTheory.TrEll.gam_charpoly_regular_cent <;> assumption)
