import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeightOffBoundaryDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedOfIsAlgPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightWeightRootChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLgOfDetSymSubLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotMemPlaceholder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquidistributionAverageOverOrbit
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_height_off_boundary_decomposition : ∀ (D : D7) (O : Setup D), O.Core → ∀ (a : ℕ → Bool) (c : O.s.Comp) (τ : D.what₂.Tau) (b : (O.var c).X),
    IsClosed ({b} : Set (O.var c).X) → (O.Φ.C c).π b ∉ GlobalTheory.Toroidal.genBd O.s.T.Z →
    (adlOf (O.Φ.C c) (O.met.hm c) (detSym O.S.Dw a none (DV.tauEmb D τ))).ht b =
      (O.adl0 c (detSym O.S.Dw a none (DV.tauEmb D τ))).ht b + (∑ σ : D.what₂.LL →+* ℂ, ∑ᶠ (z : Pts (O.var c) σ) (_ : under z = b),
          O.chg c none (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ z) /
        ((Module.finrank ℚ D.what₂.LL : ℝ) * (Nat.card {y : AlgPt (O.var c) // below y.1 = b} : ℝ)) := by
  first | exact @GlobalTheory.DetMet.det_metric | exact GlobalTheory.DetMet.det_metric | (intros; apply GlobalTheory.DetMet.det_metric <;> assumption)
