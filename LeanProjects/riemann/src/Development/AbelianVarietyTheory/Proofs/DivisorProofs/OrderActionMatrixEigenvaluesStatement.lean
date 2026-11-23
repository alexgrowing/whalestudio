import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderActionMatrixEigenvalues
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.order_action_matrix_eigenvalues : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (R : Subring ℂ) (n : ℕ)
    (ρ : orderC c →+* Module.End R (Fin n → R)) (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (B : Module.Basis (Fin n) ℂ W) (T : orderC c → Module.End ℂ W),
    (∀ a i, T a (B i) = ∑ k, ((ρ a (Pi.single i 1) k : R) : ℂ) • B k) →
    ∀ σ : E →+* FractionRing R, Module.finrank (FractionRing R) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) =
      Module.finrank ℂ (⨅ a : orderC c, Module.End.eigenspace (T a) (j (σ a)) : Submodule ℂ W) := by
  first | exact @GlobalTheory.finrank_eigK_eq_finrank_eig_complex | exact GlobalTheory.finrank_eigK_eq_finrank_eig_complex | (intros; apply GlobalTheory.finrank_eigK_eq_finrank_eig_complex <;> assumption)
