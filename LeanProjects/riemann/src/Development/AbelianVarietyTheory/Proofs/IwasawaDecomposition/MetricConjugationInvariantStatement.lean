import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationInvariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AltSumMultilinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArakelovTopUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleModelsOfHtBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmoothStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetryStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_conjugation_invariant : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (A : Adl (cxSt F) Y) (M : GlobalTheory.TrueGeo.Model Y) (L : LB M.X), L.IsLB → ∀ (m : ℕ+) (r : (L.pull M.j).ι → Y.Fnˣ), Presents ((m : ℕ) • A.D) (L.pull M.j) r → A.ci = 0 → (∀ σ, (cxSt F).mSmooth Y σ A.D (A.m σ)) → (∀ (σ σ' : F →+* ℂ) (p : Pts Y σ) (p' : Pts Y σ') (a : Y.Fnˣ), p'.1 = spMap (starRingEnd ℂ) ≫ p.1 → p ∈ Var.eqnSet σ A.D a → Var.Met.h (A.m σ') a p' = Var.Met.h (A.m σ) a p) → (∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X) (i : (L.pull M.j).ι), spMap e.O.subtype ≫ yt = y.1 ≫ M.j → ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit) → ((m : ℕ) : ℝ) * A.lg v e y = Real.log (e.w (valAt y.1 (((eqn A.D (below y.1))⁻¹ ^ (m : ℕ) * r i : Y.Fnˣ) : Y.Fn)))) → ∃ L' : GlobalTheory.HermLB M.p, A.Induced M L' m 0 := by
  first | exact @GlobalTheory.TrueGeo.ModelMetric.exists_hermLB_induced | exact GlobalTheory.TrueGeo.ModelMetric.exists_hermLB_induced | (intros; apply GlobalTheory.TrueGeo.ModelMetric.exists_hermLB_induced <;> assumption)
