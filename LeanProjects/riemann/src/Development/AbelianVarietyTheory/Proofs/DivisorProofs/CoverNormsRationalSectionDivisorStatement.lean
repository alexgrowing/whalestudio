import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverNormsRationalSectionDivisor
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOnPts
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ShFam.Pad GlobalTheory.FlatSecCover

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_norms_rational_section_divisor : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p) (φ : Y.Fn)
    (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ),
    GlobalTheory.CoverNorm.Norms V L (fun _ => φ) a l → (∀ σ, ∃ C : ℝ, ∀ y, a σ y = C) →
    letI : IsLocallyNoetherian V.X := V.ar.isLocallyNoetherian
    ∃ (r : L.B.ι → V.X.functionFieldˣ) (hr : IsRatSec L.B r),
      (∀ z, (L.div hr).mult z ≠ 0 → (V.p z).asIdeal ≠ ⊥) ∧
      ∀ σ, ∃ a : ℝ, ∀ y ∈ offSupp V.p σ (L.div hr), logNorm (L.φ σ) r y = a := by
  first | exact @GlobalTheory.CoverNorm.Lift.exists_ratSec_vertical_const | exact GlobalTheory.CoverNorm.Lift.exists_ratSec_vertical_const | (intros; apply GlobalTheory.CoverNorm.Lift.exists_ratSec_vertical_const <;> assumption)
