import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionComparisonStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ComponentHeightLowerBound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cusp_intersection_finite : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)) (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (x : ℝ), Or.𝔐.IsCuspWeight Or.sm U → CoordsAt Or.𝔐.ξ Dc.y z w → Or.PhiWeight z w x → x ≤ S'.B.ph (M.proj w) + Real.log (S'.ref.h w) := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or U M S' z w x hU hz hx
  have hw : w ∈ mcPts (mCoordIdeal Dc.y) :=
    (GlobalTheory.T.complex_points_iff_centres _ Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie w).2 ⟨z, Or.𝔐.all _, hz⟩
  haveI := LevelTowerAlt.Xo_dense Dc hw
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, h⟩ := GlobalTheory.T.cusp_intersection_comparison hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or U z w x hU hz hx (ε / 3) (by linarith)
  have hsub : Dc.Xo ⊆ mcPts (mCoordIdeal Dc.y) := fun _ h => h.1
  have h1 : ∀ᶠ w' in 𝓝[Dc.Xo] w, S'.B.ph (M.proj w') < S'.B.ph (M.proj w) + ε / 3 :=
    ((M.cont w hw).mono hsub).tendsto.eventually (LevelTowerAlt.ph_usc S'.B _ _ (by linarith))
  have hc : ContinuousWithinAt (fun w' => Real.log (S'.ref.h w')) Dc.Xo w :=
    ((S'.ref_smooth.continuousOn w hw.1).mono fun _ h => h.1.1).log (S'.ref.pos w hw.1).ne'
  have h2 : ∀ᶠ w' in 𝓝[Dc.Xo] w, Real.log (S'.ref.h w') < Real.log (S'.ref.h w) + ε / 3 :=
    hc.tendsto.eventually (gt_mem_nhds (by linarith))
  have h3 : ∀ᶠ w' in 𝓝[Dc.Xo] w, ‖w' - w‖ < δ := by
    refine mem_nhdsWithin_of_mem_nhds ?_
    filter_upwards [Metric.ball_mem_nhds w hδ] with w' hw'
    rwa [Metric.mem_ball, dist_eq_norm] at hw'
  obtain ⟨w', a, b, c', d⟩ := (h1.and (h2.and (h3.and self_mem_nhdsWithin))).exists
  have e1 := h w' d c'
  have e2 := S'.ph_eq w' ⟨d, d.1⟩
  linarith
