import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorHeightBoundNormalScheme
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartier_divisor_height_bound_normal_scheme : GlobalTheory.CovTop.Hypotheses2 → ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp (𝓞 F)) (e : ℕ),
    IsArithVar p e → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (L : HermLB p) (r : L.B.ι → X.functionFieldˣ)
    (hr : GlobalTheory.Cartier.IsRatSec L.B r), (∀ z, (L.div hr).mult z ≠ 0 → (p z).asIdeal ≠ ⊥) →
    (∀ σ, ∃ a : ℝ, ∀ y ∈ GlobalTheory.Cartier.offSupp p σ (L.div hr), GlobalTheory.Cartier.logNorm (L.φ σ) r y = a) →
    (∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ]
      [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → topSelfIntersection κ (L.B.pull i) 1 = 0) →
    ∃ (m : ℕ) (k' : Type) (_ : CommRing k') (_ : IsDomain k') (_ : Algebra (𝓞 F) k') (ρ : X ⟶ Sp k')
      (hρ : ρ ≫ spMap (algebraMap (𝓞 F) k') = p) (M : HermLB (spMap (algebraMap (𝓞 F) k'))),
      0 < m ∧ IsArithVar (spMap (algebraMap (𝓞 F) k')) 0 ∧ (L.pow m).Isometric (M.pull ρ hρ) := by
  first | exact @GlobalTheory.SteinDescent.exists_isometric_pull_stein | exact GlobalTheory.SteinDescent.exists_isometric_pull_stein | (intros; apply GlobalTheory.SteinDescent.exists_isometric_pull_stein <;> assumption)
