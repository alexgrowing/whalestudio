import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormClassesIffConjUnitaryTorusEllipticElements
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : Type) [CommRing k] [Algebra F k], ∀ (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ) (x' : plusUnits P k) (φ' : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h' : IsIsom P k J x'.1.1 φ'), ((QuotientGroup.mk x : Cls P k) = QuotientGroup.mk x' → ∃ g : HA k σ J, ∀ t, torEmb h' t = g * torEmb h t * g⁻¹) ∧ (IsConj (gam h) (gam h') → (QuotientGroup.mk x : Cls P k) = QuotientGroup.mk x') ∧ (∀ g : HA k σ J, gam h' = g * gam h * g⁻¹ → ∀ t, torEmb h' t = g * torEmb h t * g⁻¹) ∧ ∀ g : HA k σ J, HasCls P k J (g * gam h * g⁻¹) (QuotientGroup.mk x) := by
  first | exact @GlobalTheory.TrEll.cls_conj_torus | exact GlobalTheory.TrEll.cls_conj_torus | (intros; apply GlobalTheory.TrEll.cls_conj_torus <;> assumption)
