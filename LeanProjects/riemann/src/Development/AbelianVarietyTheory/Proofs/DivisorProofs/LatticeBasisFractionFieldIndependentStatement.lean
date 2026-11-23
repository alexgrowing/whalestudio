import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisFractionFieldIndependent
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
theorem _root_.GlobalTheory.T.lattice_basis_fraction_field_independent : ∀ {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)} {R : Type} [CommRing R] [IsDomain R]
    {L : Type} [Field L] [Algebra R L] (j : FractionRing R →+* L)
    (hj : ∀ x : R, j (algebraMap R (FractionRing R) x) = algebraMap R L x) {n : ℕ} {V : Type*} [AddCommGroup V]
    [Module L V] (β : (Fin n → R) →ₛₗ[algebraMap R L] V)
    (hβ : LinearIndependent L (fun k ↦ β (Pi.single k 1)) ∧ Submodule.span L (Set.range fun k ↦ β (Pi.single k 1)) = ⊤)
    (ρ : orderC c →+* Module.End R (Fin n → R)) (T : orderC c → Module.End L V)
    (hT : ∀ a x, β (ρ a x) = T a (β x)) (N : Submodule R (Fin n → R)) {I : Type} [Fintype I]
    (σ : I → E →+* FractionRing R)
    (h : Submodule.span L (β '' (N : Set (Fin n → R))) = ⨆ i, ⨅ a : orderC c, Module.End.eigenspace (T a) (j (σ i a))),
   N.baseChange (FractionRing R) = ⨆ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ (σ i) := by
  first | exact @GlobalTheory.EigDescentFrac.baseChange_eq_iSup_eigK | exact GlobalTheory.EigDescentFrac.baseChange_eq_iSup_eigK | (intros; apply GlobalTheory.EigDescentFrac.baseChange_eq_iSup_eigK <;> assumption)
