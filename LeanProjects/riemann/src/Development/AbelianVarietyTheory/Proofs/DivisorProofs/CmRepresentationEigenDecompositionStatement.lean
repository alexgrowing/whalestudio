import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRepresentationEigenDecomposition
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
theorem _root_.GlobalTheory.T.cm_representation_eigen_decomposition : ∀ (E : Type) [Field E] [NumberField E] (O : Subring E), (∀ x : E, ∃ n : ℕ, n ≠ 0 ∧ (n : E) * x ∈ O) →
    ∀ (L : AddSubgroup E), (∀ a ∈ O, ∀ x ∈ L, a * x ∈ L) →
    ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (P : L →+ W), Submodule.span ℂ (Set.range P) = ⊤ →
      Module.finrank ℂ W = Module.finrank ℚ E →
    ∀ (T : O → Module.End ℂ W), (∀ (a : O) (x y : L), (y : E) = a * x → T a (P x) = P y) →
    ∀ τ : E →+* ℂ, Module.finrank ℂ (⨅ a : O, Module.End.eigenspace (T a) (τ a) : Submodule ℂ W) = 1 := by
  first | exact @GlobalTheory.EigLine.finrank_common_eigenspace_eq_one | exact GlobalTheory.EigLine.finrank_common_eigenspace_eq_one | (intros; apply GlobalTheory.EigLine.finrank_common_eigenspace_eq_one <;> assumption)
