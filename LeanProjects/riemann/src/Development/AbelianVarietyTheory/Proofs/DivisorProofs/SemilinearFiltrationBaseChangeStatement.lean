import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearFiltrationBaseChange
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
theorem _root_.GlobalTheory.T.semilinear_filtration_base_change : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M] {M' : Type*} [AddCommGroup M'] [Module R' M']
    (f : M →ₛₗ[algebraMap R R'] M') (hf : Function.Bijective (liftSemi f)) (F : Submodule R M)
    (hF : ∃ N : Submodule R M, IsCompl F N) (F' : Submodule R' M') (hF' : F' = Submodule.span R' (f '' (F : Set M)))
    (g : Module.Dual R M →ₛₗ[algebraMap R R'] Module.Dual R' M') (hg : ∀ h c, g h (f c) = algebraMap R R' (h c)),
   Submodule.span R' (g '' (F.dualAnnihilator : Set (Module.Dual R M))) = F'.dualAnnihilator := by
  first | exact @GlobalTheory.annihilator_baseChange | exact GlobalTheory.annihilator_baseChange | (intros; apply GlobalTheory.annihilator_baseChange <;> assumption)
