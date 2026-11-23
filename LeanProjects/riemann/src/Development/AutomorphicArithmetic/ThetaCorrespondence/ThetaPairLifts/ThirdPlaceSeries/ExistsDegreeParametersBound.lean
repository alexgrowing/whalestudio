import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsDegreeParametersBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LogDegreeLeOfCoveringRange
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HilbertSamuelBergmanFrameBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HermitianPairingBilinearOnPair
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtBigRun
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPointStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizesOfCoverStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShortVectorsSpanCuspLattice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShortVectorWeightBound

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
namespace GlobalTheory.HSShortRun
open GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.HSCore
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
variable {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j}
set_option maxHeartbeats 1000000 in
theorem hsClaim_short_alt_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ n Λ β ΛD ΛT J : ℝ, 1 ≤ n ∧ 1 ≤ Λ ∧ 1 ≤ β ∧ 1 ≤ ΛD ∧ 1 ≤ ΛT ∧ Real.log n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ Real.log ΛD ≤ PP * kap p i ∧ Real.log ΛT ≤ PP * kap p i ∧ J ≤ 4 * (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1) + lenT p i PP * PP) + 2 * PP * (kap p i / lenT p i PP) * CompHt.dimFlag (dat p i) ∧ Formalism.NormVectorIdentities.Items.HSClaimS 26 (lenT p i PP) (CompHt.dimFlag (dat p i)) n 1 Λ β ΛD ΛT J (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.ht (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.rkC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) (Y.degC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) := by
  intro hX h2 hG hQ hS hK hL hDG hSz hF
  have hP := _root_.GlobalTheory.T.covering_topology_refinement h2
  have H₄ := _root_.GlobalTheory.T.covering_domain_lattice_regularity h2
  have H₃ : _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Y.dg
      (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP := by
    apply _root_.GlobalTheory.T.log_dg_u1_le_of_flatDeg <;> assumption
  refine Closed.imp (Closed.and (Closed.and (Closed.and (_root_.GlobalTheory.T.hilbertSamuel_bergman_frame_bound_alt h2 hDG hSz hF) (_root_.GlobalTheory.T.birOn_weightPair_both_components_alt hX hG hQ hS h2 hSz))
    (Closed.and H₃ _root_.GlobalTheory.HSApp.wtBig_run_alt)) (Closed.and (Closed.and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hSz) (_root_.GlobalTheory.T.size_bounds_for_family_alt hSz))
    (Closed.and (_root_.GlobalTheory.T.short_vectors_span_cusp_lattice_alt h2 hDG hSz hF) (_root_.GlobalTheory.T.short_path_weight_bound_alt h2 hDG hSz hF)))) ?_
  rintro eps Fm CH - ⟨⟨⟨⟨_, -, a₁⟩, _, -, a₂⟩, ⟨_, -, a₃⟩, _, -, a₄⟩, ⟨⟨_, -, a₅⟩, _, -, a₆⟩, ⟨_, -, a₇⟩, _, -, a₈⟩
  obtain ⟨x0, a⟩ := (((a₁.and a₂).and (a₃.and a₄)).and ((a₅.and a₆).and (a₇.and a₈)))
  clear a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY Z => ?_⟩
  obtain ⟨⟨⟨a₁, a₂⟩, a₃, a₄⟩, ⟨a₅, a₆⟩, a₇, a₈⟩ := a x hx hle ι p hp
  clear a
  obtain ⟨⟨f₂⟩, f₁, Λ, β, hΛ, hβ, hn, hlβ, hlΛ, hfr, hberg⟩ := a₁ i hi Y hY Z
  have hW := a₄ i hi
  obtain ⟨hp1, hq1, hE, -⟩ := a₅ i hi
  obtain ⟨hLaw, hIn, -, -, -, -, -, -, -, -, -, -, hPP, -⟩ := a₆ i hi Y hY
  obtain ⟨hPk, hsh⟩ := a₈ i hi Y hY
  have hg := gapGe_wt_of_wtBig hW
  have hPP0 : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hPP
  have hκ0 : 0 ≤ kap p i :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨c₁, c₂⟩ := _root_.GlobalTheory.HSShortRun.hilbertSamuel_estimate_at_level hP hG hQ h2.q15 h2.q16 hS hK.toroidalChartsForFan hL hY.1 hE Z hW
    (fun j _ => (H₄ _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY.1 _ (fun τ => antitone_of_gapGe (by positivity) (hg j) τ)
      (fun τ => le_trans (by omega) (hg j τ ((dat p i).p - 1) (by omega)))).1)
    hPP0 hκ0 f₂ f₁ hΛ hβ hfr hberg (a₂ i hi Y hY Z) (a₇ i hi Y hY Z) (hsh Z)
  refine ⟨f₁.n, Λ, β, _, _, _, c₁, hΛ, hβ, Real.one_le_exp hPk, Real.one_le_exp hPk, hn, hlβ, a₃ i hi Y hY Z, hlΛ,
    (Real.log_exp _).le, (Real.log_exp _).le, ?_, c₂⟩
  have e₁ : 0 ≤ CompHt.dimFlag (dat p i) * (Fm.parT x hx ι).PP * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
    positivity
  have e₂ : 0 ≤ (lenT p i (Fm.parT x hx ι).PP : ℝ) * (Fm.parT x hx ι).PP := by positivity
  have e₃ : 0 ≤ 2 * (Fm.parT x hx ι).PP * (kap p i / lenT p i (Fm.parT x hx ι).PP) * CompHt.dimFlag (dat p i) := by
    positivity
  linarith
end GlobalTheory.HSShortRun
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degree_parameters_bound_alt_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ n Λ β ΛD ΛT J : ℝ, 1 ≤ n ∧ 1 ≤ Λ ∧ 1 ≤ β ∧ 1 ≤ ΛD ∧ 1 ≤ ΛT ∧ Real.log n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ Real.log ΛD ≤ PP * kap p i ∧ Real.log ΛT ≤ PP * kap p i ∧ J ≤ 4 * (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1) + lenT p i PP * PP) + 2 * PP * (kap p i / lenT p i PP) * CompHt.dimFlag (dat p i) ∧ Formalism.NormVectorIdentities.Items.HSClaimS 26 (lenT p i PP) (CompHt.dimFlag (dat p i)) n 1 Λ β ΛD ΛT J (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.ht (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.rkC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) (Y.degC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) := by
  first | exact @_root_.GlobalTheory.HSShortRun.hsClaim_short_alt_alt | exact _root_.GlobalTheory.HSShortRun.hsClaim_short_alt_alt | (intros; apply _root_.GlobalTheory.HSShortRun.hsClaim_short_alt_alt <;> assumption)
end
end
