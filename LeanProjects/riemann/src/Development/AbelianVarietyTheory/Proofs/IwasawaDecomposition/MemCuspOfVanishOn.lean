import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicFlowMajorantCauchySchwarzStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlowOrbitFirstMinimumOfIsotropicFlowMajorantStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KoecherPrincipleFlagDomainFrequenciesNonnegStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MaximumPrincipleIsotropicFlowRescaledBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModerateGrowthOfFirstMinimumAndFlowBoundsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FourierJacobiConstantTermEqZeroOfFlowLineStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedIsSecZeroKeySection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincipalCMTripleExponentialOfPeriodStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexArcOfAnalyticModelOnFlowOrbitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcsOnFlowLinesOfAnalyticModelOnOrbitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantVectorsLieBasisOfComplexArcStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcFramedPointExtendsToModelBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryExtensionIndependentOfModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenspaceFrameLocalRingBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeBaseChangeLocalRingsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRulBC
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmArcDataAtSplitIsotropicPoint
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCoeffNeZeroOfFourierJacobiArcDatum
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsArcFr
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumEqZeroOfRankZero
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoWeightStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountAsmPfB

noncomputable section

namespace GlobalTheory.CuspFrom

section Analytic

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {la : Wt X.Ψ r}
  {P : Frame X.Ψ r → ℂ}

theorem thickBdd (hP : X.IsSec la P) : ThickBdd X (X.pnorm la P) := by
  intro ε hε
  obtain ⟨K, hK, hKd, hcov⟩ := GlobalTheory.FlagMahler.mahler_compactness (E := E) r X ε hε
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn ((AR.Up.BigB.pnorm_contOn X la hP).mono hKd)).bddAbove
  refine ⟨C, fun x hx hl => ?_⟩
  obtain ⟨γ, hγ, b, hb, h⟩ := hcov x hx hl
  have := hC ⟨_, h, rfl⟩
  rwa [AR.Up.OW.pnorm_lact la hP hγ (AR.Up.OntoS.dom_rmul X hx hb), FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx b hb] at this

theorem freqNonneg (hf : 1 < Module.finrank ℚ E / 2) (hP : X.IsSec la P) : FreqNonneg X la P :=
  GlobalTheory.T.koecher_principle_flagDomain_frequencies_nonneg (GlobalTheory.T.flowOrbitFirstMinimum_of_isotropicFlowMajorant GlobalTheory.T.isotropicFlow_majorant_cauchySchwarz) E r X la P hf hP (thickBdd X hP)

theorem growth (hf : 1 < Module.finrank ℚ E / 2) (hP : X.IsSec la P) {w : ℝ} (hw : 0 ≤ w)
    (h : ∀ τ, X.spread la τ / 2 ≤ w) : ∃ C A : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C * X.la1 x ^ (-(A * w)) :=
  GlobalTheory.T.moderate_growth_of_firstMinimum_and_flow_bounds GlobalTheory.T.isotropicFlow_majorant_cauchySchwarz E r X w _ hw (fun x _ => mul_nonneg (norm_nonneg _) (Formalism.L2.Pj.pnorm_fac_nonneg X la x))
    (thickBdd X hP) (GlobalTheory.T.maximum_principle_isotropicFlow_rescaledBound E r X la P w hP (freqNonneg X hf hP) h)

theorem isModerate (hf : 1 < Module.finrank ℚ E / 2) (hP : X.IsSec la P) : X.IsModerate la P := by
  obtain ⟨C, A, h⟩ := growth X hf hP (w := ∑ τ, |X.spread la τ / 2|) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    fun τ => (le_abs_self _).trans (Finset.single_le_sum (f := fun τ => |X.spread la τ / 2|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  exact ⟨C, _, h⟩

end Analytic

section Geometric

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam
open scoped LaurentSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}

theorem exists_input [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (Uw : UnfWit U)
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) {k : U.Comp} {ξ' : Fin r → E}
    (hξ : (U.X k).IsIso ξ') {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) :
    ∃ a : ArcIn Dw l (RingHom.id c.F) ℂ σ, ∀ (O : Type) [CommRing O] (β : O →+* c.F),
      FlowTie Uw (a.restrict β) k ξ' x := by
  letI := H.starRing
  obtain ⟨hp, hq⟩ := GlobalTheory.ArcCM.Exist.one_le_of_isIso hU hξ
  obtain ⟨A, gam, ξ, jj, DB, tyB, eB, hO, hξ0, hrk, hdvd, -, hprim, -, hab, hDp, hDq⟩ :=
    GlobalTheory.T.exists_analytic_model_on_frame_orbit_isolating E H Dw l Xo c σ r U Uw k ξ' x 0 0 hσ hU hξ hx
      (fun m _ => ⟨0, by simp, by funext τ i; simp [Data.embV, Data.emb]⟩) (by simp [cc]) (by simp)
      (fun s _ _ => ⟨0, by simp⟩)
  obtain ⟨B, ex, hex⟩ := GlobalTheory.T.exists_principalCMTriple_exponential_of_period E H l DB _ tyB _ hab.2.1 hab.2.2.2.2
  obtain ⟨aC, Λ, hA, h1, h2⟩ := GlobalTheory.T.exists_complex_arc_of_analytic_model_on_flow_orbit E H Dw l Xo c σ r U Uw k ξ' x B hσ hU A gam ξ DB tyB eB ex hO hrk hdvd
    hprim hab hDp hDq hp hq hex
  subst hA
  exact ⟨aC, GlobalTheory.T.arcs_on_flow_lines_of_analytic_model_on_orbit E H Dw l Xo c σ r U Uw k ξ' x aC Λ hσ hU hξ hx gam ξ hO hξ0 hrk h1 h2⟩

theorem exists_model (Xo : Moduli Dw l) (c : Coeff l) (hr : 1 ≤ Dw.p + Dw.q) :
    ∃ (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype), Y.N4 ∧ PushInvertible Y.t.G Y.t.PP.L := by
  classical
  have hK := GlobalTheory.ArcCM.known_holds
  obtain ⟨W, hW⟩ := GlobalTheory.GlobalModelGuards.exists_place 2 Nat.prime_two
  have hg : l.GoodAt 2 := by
    have := l.three_le
    rwa [Level.GoodAt, Nat.factorization_eq_zero_of_not_dvd l.odd.not_two_dvd_nat, pow_zero, Nat.div_one]
  have key : ∀ Xs : ∀ l' : Level H, Moduli Dw l',
      ∃ Y : Model (Xs l) c (c.V W).subtype, Y.N4 ∧ PushInvertible Y.t.G Y.t.PP.L := by
    intro Xs
    obtain ⟨Y, hY, -⟩ := hK.models.2 E H Dw hr Xs
    obtain ⟨h2, h4⟩ := hY 2 W Nat.prime_two hW
    exact ⟨Y 2 W Nat.prime_two hW ⟨l, c, hg⟩, (h4 _).2.2, (h2.1 ⟨l, c, hg⟩).2.2.1⟩
  have h := key (Function.update (fun l' => Classical.choice (hK.n1ab E H Dw l' hr)) l Xo)
  rw [Function.update_self] at h
  exact ⟨W, h⟩

theorem coeff_eq_zero {v : PowerSeries ℂ} (hv : v ∈ IsLocalRing.maximalIdeal (PowerSeries ℂ)) {j : ℤ} (hj : j ≤ 0) :
    (algebraMap (PowerSeries ℂ) ℂ⸨X⸩ v).coeff j = 0 := by
  rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at hv
  rw [LaurentSeries.coe_algebraMap, PowerSeries.coeff_coe]
  split_ifs with h0
  · rfl
  · obtain rfl : j = 0 := by omega
    simpa using hv

end Geometric

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped LaurentSeries

end GlobalTheory.CuspFrom
