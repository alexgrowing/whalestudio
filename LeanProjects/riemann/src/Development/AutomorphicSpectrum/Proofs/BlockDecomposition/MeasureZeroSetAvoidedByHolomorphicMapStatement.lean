import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureZeroSetAvoidedByHolomorphicMap
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackIsPotentialStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackChartFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticoneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroLocusRegularFunctionNullStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DehomogenizedEvalEqRatioStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedFormNonzeroOnGenericPointStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_zero_set_avoided_by_holomorphic_map : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ (Z : Set (GlobalTheory.CxPts q σ)), MeasurableSet Z →
    (∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0) →
    (∀ y, y ∉ Z → ∃ x, F x = y) → (∀ x x', F x ∉ Z → F x = F x' → x = x') →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → ∀ (ε : ℤˣ) (K : Fin A.n → Set (Fin D → ℂ)),
    (∀ j, IsCompact (K j)) → (∀ j, K j ⊆ (A.chart j).target) →
    (∀ x, ∃ j, ∃ u ∈ K j, (A.chart j).symm u = x) →
    φ.chernPart D ε ≤ ∑ j, Measure.map (F ∘ (A.chart j).symm)
      ((volume.restrict (K j \ (F ∘ (A.chart j).symm) ⁻¹' Z)).withDensity fun u =>
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u|) := by
  first | exact @GlobalTheory.CompanionTheory.ArchDom.chernPart_le_sum_map | exact GlobalTheory.CompanionTheory.ArchDom.chernPart_le_sum_map | (intros; apply GlobalTheory.CompanionTheory.ArchDom.chernPart_le_sum_map <;> assumption)
