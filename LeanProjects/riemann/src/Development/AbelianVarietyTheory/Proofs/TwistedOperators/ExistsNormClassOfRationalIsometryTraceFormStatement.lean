import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNormClassOfRationalIsometryTraceForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normClass_of_rationalIsometry_traceForm : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (P : PPol σ n) (J : Matrix (Fin n) (Fin n) E) (φ : Fld P ≃ₗ[E] (Fin n → E)) (x : Fld P), x ≠ 0 → star' P x = x → (∀ y y', Formalism.UG.hform (σ : E →+* E) J (φ y') (φ y) = Algebra.trace E (Fld P) (x * y * star' P y')) → ∀ γ : GRat σ J, (∀ y, γ.1.1 *ᵥ φ y = φ (alpha P * y)) → ∃ q, HasCls P F J (diagH σ J F γ) q := by
  first | exact @GlobalTheory.RatCls.hasCls_of_ratIsom | exact GlobalTheory.RatCls.hasCls_of_ratIsom | (intros; apply GlobalTheory.RatCls.hasCls_of_ratIsom <;> assumption)
