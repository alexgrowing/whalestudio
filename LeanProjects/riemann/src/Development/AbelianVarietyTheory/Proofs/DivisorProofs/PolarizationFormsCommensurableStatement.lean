import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormsCommensurable
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
theorem _root_.GlobalTheory.T.polarization_forms_commensurable : GlobalTheory.Published.AbelianDeRham → ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R : Type) [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (c c₀ : 𝔠.elt), (c₀ : F) ≠ 0 → ∀ ψ ψ₀ : LinearMap.BilinForm R (HdR X.A),
    IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ → IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c₀) ψ₀ →
    ∃ (n : ℕ) (t : 𝓞 F), n ≠ 0 ∧ ∀ x y, (n : R) * ψ x y = ψ₀ x (act (dp0 R) (𝟙 _) X.rm t y) := by
  first | exact @GlobalTheory.RealMult.PolScale.exists_nat_mul_polForm_eq | exact GlobalTheory.RealMult.PolScale.exists_nat_mul_polForm_eq | (intros; apply GlobalTheory.RealMult.PolScale.exists_nat_mul_polForm_eq <;> assumption)
