import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverWithInducedNorms
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLgOfLnSymUpdateSubLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverInducedMetricsArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightBoundedByPrimeWeights
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.LocM
open GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open GlobalTheory.PairTerm
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cover_with_induced_norms : GlobalTheory.Published.ArCalc → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (ι : Type) [Fintype ι]
    (A : ι → Adl (cxSt F) Y) (L : ι → HermLB M.p) (m : ℕ+) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ),
    (∀ i, (A i).Induced M (L i) m 0) → (haveI := M.ar.isIntegral; IsArFun L Y.dim Ψ) →
    ∃ (V : Cover Y) (L' : ι → HermLB V.p),
      (∀ i, Norms V (L' i) (fun x => genAt (A i).D x ^ (m : ℕ)) (fun σ y => (m : ℕ) * lnAdl (A i) σ y)
        (fun v e y => (m : ℕ) * (A i).lg v e y)) ∧ IsArFun L' Y.dim ((V.deg : ℝ) • Ψ) := by
  first | exact @GlobalTheory.VertPassDeg.passDeg | exact GlobalTheory.VertPassDeg.passDeg | (intros; apply GlobalTheory.VertPassDeg.passDeg <;> assumption)
