import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyUnitaryTorusOrbitalClassTrivialLocal
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsLattice E L], ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (1 : Cls P (Fv F v)) ∈ XSet P (Fv F v) J ∧ (∀ (γ : GLoc σ J v) q, HasCls P (Fv F v) J γ q → (∃ g, g⁻¹ * γ * g ∈ stabLoc σ J L v) → q = 1) ∧ (∀ (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin r → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), gam h ∈ stabLoc σ J L v → ∀ t, torEmb h t ∈ stabLoc σ J L v ↔ t ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v) ∧ ∀ (μ : Measure (GLoc σ J v)) (dt : Measure (Tor P (Fv F v))), μ.IsHaarMeasure → dt.IsHaarMeasure → μ (stabLoc σ J L v) = 1 → dt (stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v) = 1 → ∀ q : XSet P (Fv F v) J, (q.1 = 1 → orbCls μ dt (unitLoc σ J L v) q = 1) ∧ (q.1 ≠ 1 → orbCls μ dt (unitLoc σ J L v) q = 0) := by
  first | exact @GlobalTheory.TrEll.eventually_unitLoc_orbCls | exact GlobalTheory.TrEll.eventually_unitLoc_orbCls | (intros; apply GlobalTheory.TrEll.eventually_unitLoc_orbCls <;> assumption)
