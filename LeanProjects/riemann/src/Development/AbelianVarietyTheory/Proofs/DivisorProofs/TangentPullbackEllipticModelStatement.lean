import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackEllipticModel
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_pullback_elliptic_model : ∀ (R : Type) [CommRing R] (σ : R →+* ℂ) (P : Out.PolAV (Sp R)) (A' : Over (Sp ℂ)) [GrpObj A']
    (φ' : A'.left ⟶ P.A.left) (L' : LB A'.left) (u : HolUnif A' L' 1) (v : epsR R ⟶ P.A) (v' : epsR ℂ ⟶ A') (t : ℂ)
    (S : Set ℂ), IsAbelianScheme A' → SmoothOfRelativeDimension 1 A'.hom → IsGrpPullback A' P.A (spMap σ) φ' →
    (∀ w, w ∈ u.Λ ↔ w 0 ∈ S) → IsTangent v → IsTangent v' → v'.left ≫ φ' = spMap (Chart.dualMapR σ) ≫ v.left →
    u.IsDiff (fun _ ↦ t) v' → ∀ (g : ℕ) (j₀ : Fin g),
    ∃ (P₀ : Out.PolAV (Sp R)) (A₀ : Over (Sp ℂ)) (_ : GrpObj A₀) (φ₀ : A₀.left ⟶ P₀.A.left) (L₀ : LB A₀.left)
      (u₀ : HolUnif A₀ L₀ g) (v₀ : epsR R ⟶ P₀.A) (v₀' : epsR ℂ ⟶ A₀),
      IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension g A₀.hom ∧ IsGrpPullback A₀ P₀.A (spMap σ) φ₀ ∧
      (∀ w, w ∈ u₀.Λ ↔ ∀ j, w j ∈ S) ∧ IsTangent v₀ ∧ IsTangent v₀' ∧
      v₀'.left ≫ φ₀ = spMap (Chart.dualMapR σ) ≫ v₀.left ∧ u₀.IsDiff (Pi.single j₀ t) v₀' := by
  first | exact @GlobalTheory.PowFibre.exists_pow | exact GlobalTheory.PowFibre.exists_pow | (intros; apply GlobalTheory.PowFibre.exists_pow <;> assumption)
