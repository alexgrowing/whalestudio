import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShareStatementOfKnownTheorems
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ValuationMultiplicityOfConsecutiveRun
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BirOnWeightPairBothComponents
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TwistedFlatBundleRanks
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ProportionalityPrincipleCompactification
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CompactificationTopChernEqVolume
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.JetRankComplexLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsWeightHodgeBundleGenerated
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HodgeBundleIsNefIsBigOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShareStatementOfPrintsStatement

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop.ShareRowsNef
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
theorem nef_share_lower_bound (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hSI : GlobalTheory.Published.SiegelToroidalIntegral) (hKS : GlobalTheory.Published.ToroidalForFanKS)
    (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted) (hSL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : CoreJ D}
    (hT : LawsJ T) {j : ℕ} (hp : 1 ≤ (T.Q.Dw j).p) (hq : 1 ≤ (T.Q.Dw j).q) (hf : 2 < Module.finrank ℚ D.host.E / 2) (hj : InR D j)
    (Y : Deep T.toCore j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (P : WtPar (T.Q.Dw j)) (hB : WtBig P)
    (Z : Comp Y.d.Xo₂ Y.d.c₂) (hbir : BirOn Y.U Z (wtOf _ P.u₁ 0)) :
    (((P.T - 1).choose (CompHt.dimFlag (T.Q.Dw j)) : ℕ) : ℝ) * Y.dg P.u₁ Z ≤ Y.rkC (P.wt P.T) Z := by
  have hP1 := _root_.GlobalTheory.T.covering_topology_refinement hP
  obtain ⟨g1, g2, g3⟩ := gapGe_of_wtBig hB
  have good : ∀ la, GapGe 1 la → _ := fun la h =>
    _root_.GlobalTheory.T.covering_domain_lattice_regularity hP D T hT j hp hq hf hj Y e o hY la (antitone_of_gapGe hp hq h).1 (antitone_of_gapGe hp hq h).2
  obtain ⟨TF, R, ω, h⟩ := _root_.GlobalTheory.T.exists_weight_hodge_bundle_generated hP1 hG hQ hP.q15 hP.q16 hSI hKS.toroidalChartsForFan hSL D T.toCore j Y e o hY hf Z P hB fun i _ => (good _ (g3 i)).1
  obtain ⟨f₁⟩ := nonempty_cuspFrame ((good _ g1).2 Z)
  obtain ⟨f₂⟩ := nonempty_cuspFrame ((good _ g2).2 Z)
  let k : CompHS.Consts := ⟨1, 1, 1, 1, 1, le_rfl, le_rfl, le_rfl⟩
  let th : R.L.Sec := GlobalTheory.CompHS.toSec (R.Δ₁.lift 0)
  have hA := _root_.GlobalTheory.T.hodge_bundle_isNef_isBig_of_weight hP1 hQ.nef hSI hKS.toroidalChartsForFan hSL _ _ _ _ _ _ TF Z _ Y.U P R ω _ D _ _ h f₁ f₂ th k hY.geo hB
  have a3 := GlobalTheory.T.hilbertSamuel_map_birational_of_cuspForms_generate TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k (GlobalTheory.T.cuspForm_ratios_generate_at_flagSpace_genericPoint TF.X Z Y.U P.u₁ ⟨R.toModif⟩ hbir)
  obtain ⟨a1, a2⟩ := hA
  have key := GlobalTheory.T.choose_mul_componentDegree_le_dimension hQ _ _ _ _ _ _ _ _ Z _ Y.U P R ω _ D _ _ h f₁ f₂ th k a1 a2 a3
  have hr : rankOn Y.U Z (wtOf _ (P.wt P.T) 0) = Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf _ (P.wt P.T) 0)) := by
    rw [rankOn, Formalism.HN.rkK, ((good _ (g3 P.T)).2 Z).2.2, finrank_top]
  rw [← hr] at key
  exact_mod_cast key
theorem nef_share_upper_bound (hX : GlobalTheory.CovTop.HypothesesX) (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hSI : GlobalTheory.Published.SiegelToroidalIntegral) (hKS : GlobalTheory.Published.ToroidalForFanKS) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hSL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : CoreJ D}
    (hT : LawsJ T) {j : ℕ} (hp : 1 ≤ (T.Q.Dw j).p) (hq : 1 ≤ (T.Q.Dw j).q) (hf : 2 < Module.finrank ℚ D.host.E / 2) (hj : InR D j)
    (Y : Deep T.toCore j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (P : WtPar (T.Q.Dw j)) (hB : WtBig P)
    (hs : ∀ τ, StrictAnti (P.u₁ τ) ∧ StrictAnti (CompHt.uPrime _ P.u₁ τ))
    (hbir : ∀ Z, BirOn Y.U Z (wtOf _ P.u₁ 0))
    (hV : ∀ Z, ValMult Y.U Z (wtOf _ P.u₁ 0) (wtOf _ (CompHt.uPrime _ P.u₁) 0))
    (h0 : 0 ≤ CompHt.rhoB _ P.u₁) (h1 : CompHt.rhoB _ P.u₁ ≤ 1 / 2) (la : AllWt.Weight (T.Q.Dw j)) (hla : ∀ τ, Antitone (la τ))
    (hd : ∀ τ, Antitone (((P.T + CompHt.dimFlag (T.Q.Dw j) + 3 : ℕ) : ℤ) • P.u₁ τ - la τ))
    (Z : Comp Y.d.Xo₂ Y.d.c₂) (hδ : 0 < Y.dg P.u₁ Z) :
    (1 - 7 * ((CompHt.dimFlag (T.Q.Dw j) : ℝ) ^ 2 / P.T + CompHt.dimFlag (T.Q.Dw j) * CompHt.rhoB _ P.u₁)) * Y.rkC la Z ≤
      (((P.T - 1).choose (CompHt.dimFlag (T.Q.Dw j)) : ℕ) : ℝ) * Y.dg P.u₁ Z := by
  have hD := GlobalTheory.CompHS.dimFlag_eq (T.Q.Dw j)
  have hg := hB.gaps
  have hT1 := hB.le_T
  have hD2 := two_le_dimFlag hp hq hf
  rw [← hD] at hg hT1 hD2
  have hle := (GlobalTheory.T.componentImageDegree_between_of_proportionality _ _ _ _ _ _ _ Y.U hY.unf (_root_.GlobalTheory.T.proportionality_principle_compactification hP hSI hKS hSL D T hT j hp hq hf hj Y e o hY).1
    (_root_.GlobalTheory.T.compactification_top_chern_eq_volume hP hSI hKS hSL D T hT j hp hq hf hj Y e o hY) P.u₁ (fun τ => (hs τ).1) (fun τ => (hs τ).2) hbir hV Z Z).1
  rw [CompHt.delPrime_eq _ _ (CompHt.vdm_pos fun τ => (hs τ).1).ne'] at hle
  set ρ := CompHt.rhoB _ P.u₁ with hρ
  set n := P.T + CompHt.dimFlag (T.Q.Dw j) + 3 with hn
  have hρ1 : 0 < 1 - ρ := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha1 : ((⌊(n : ℝ) / (1 - ρ)⌋₊ : ℕ) : ℝ) ≤ n / (1 - ρ) := Nat.floor_le (by positivity)
  have ha2 : (n : ℝ) / (1 - ρ) < (⌊(n : ℝ) / (1 - ρ)⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one _
  have ha3 : n ≤ ⌊(n : ℝ) / (1 - ρ)⌋₊ := Nat.le_floor (by rw [le_div_iff₀ hρ1]; nlinarith)
  have hjet := _root_.GlobalTheory.T.jet_rank_complex_le hX hP hSI hKS hG hQ hSL D T hT j hp hq hf hj Y e o hY Z P.u₁ la n ⌊(n : ℝ) / (1 - ρ)⌋₊ hg hla hd (by
    have h2 : CompHt.topDeg Y.U Z P.u₁ ≤ Y.dg P.u₁ Z / (1 - ρ) := by
      rw [le_div_iff₀ hρ1, mul_comm]; exact hle
    calc (n : ℝ) * CompHt.topDeg Y.U Z P.u₁ ≤ n * (Y.dg P.u₁ Z / (1 - ρ)) := mul_le_mul_of_nonneg_left h2 hn0
      _ = n / (1 - ρ) * Y.dg P.u₁ Z := by ring
      _ < _ := mul_lt_mul_of_pos_right ha2 hδ)
  refine GlobalTheory.share_bound_of_jet_count _ _ _ ρ _ _ hD2 hT1 h0 h1 ha3 ?_ hδ.le (Nat.cast_nonneg _) hjet
  rw [hn] at ha1 ⊢
  push_cast at ha1 ⊢
  exact ha1
theorem share_of_deg : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS →
    GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative →
    DeepGood → Size → FlatDeg → Deg → Share := by
  intro hX hP hSI hKS hG hQ hSL hDG hS hF hD
  have h1 := hS
  have h2 := hF
  have h3 := hD
  have h4 := GlobalTheory.T.size_bounds_for_family hS
  have h5 := _root_.GlobalTheory.T.valuation_multiplicity_run_estimate hP hG hQ hSI hKS hSL hDG hS hF
  have h6 := _root_.GlobalTheory.T.birOn_weightPair_both_components hX hG hQ hSI hP hS
  unfold Size at h1
  unfold FlatDeg Covers at h2
  unfold Deg Covers at h3
  unfold Covers at h4 h5 h6
  have all := lifts_and (lifts_and (lifts_and (lifts_and h1 h2) (lifts_and h3 wtBig_run))
    (lifts_and (GlobalTheory.T.weight_parameter_strict_antitone hS) h4)) (lifts_and h5 h6)
  clear h1 h2 h3 h4 h5 h6
  refine Closed.imp all fun Fm _ _ ⟨C, hC, x0, h⟩ => ⟨C, hC, x0, fun x hx hle ι p hp i hi Y hY u1 hu Z => ?_⟩
  obtain ⟨⟨_, ⟨_, ⟨_, ⟨_, hs⟩, _, hfl⟩, _, ⟨_, hdg⟩, _, hB⟩, _, ⟨_, hq⟩, _, hz⟩, _, ⟨_, hv⟩, _, hbi⟩ := h x hx hle ι p hp i
  obtain ⟨hp1, hq1, hf, hqu, hsa, ⟨w, -, hw⟩, hdom⟩ := hq hi
  obtain ⟨hT, hj, -⟩ := hz hi Y hY
  obtain ⟨-, h0, -, hz1⟩ := (hs.2.2.2.2.2.2 hi).2 u1 hu
  obtain ⟨δ, hδ, hδ2⟩ := hdg hi Y hY u1 hu
  obtain rfl := hqu u1 hu
  have htw := (_root_.GlobalTheory.T.twisted_flat_bundle_ranks hP _ p.T hT _ hp1 hq1 hf hj Y _ _ hY.1 _ (hfl hi Y hY)).1
  refine ⟨?_, ?_⟩
  · rw [hw, htw]
    exact _root_.GlobalTheory.CovTop.ShareRowsNef.nef_share_lower_bound hP hSI hKS hG hQ hSL hT hp1 hq1 hf hj Y hY.1 _ (hB hi) Z (hbi hi Y hY Z).1
  · have hD2 : (2 : ℝ) ≤ CompHt.dimFlag (dat p i) := by
      rw [GlobalTheory.CompHS.dimFlag_eq]; exact_mod_cast two_le_dimFlag hp1 hq1 hf
    refine _root_.GlobalTheory.CovTop.ShareRowsNef.nef_share_upper_bound hX hP hSI hKS hG hQ hSL hT hp1 hq1 hf hj Y hY.1 _ (hB hi) hsa (fun Z => (hbi hi Y hY Z).1) (hv hi Y hY) h0 ?_ (uM p i) (fun τ => ?_) (fun τ => ?_) Z
      (hδ.trans_le (hδ2 Z).1)
    · unfold zed at hz1
      have : 0 ≤ (CompHt.dimFlag (dat p i) : ℝ) ^ 2 / lenT p i (Fm.parT x hx ι).PP := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hD2 h0]
    · simpa using (hdom 0 (by norm_num) τ).1
    · simpa using (hdom 0 (by norm_num) τ).2
end GlobalTheory.CovTop.ShareRowsNef
end
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
theorem _root_.GlobalTheory.T.share_of_prints_deg_flatDeg : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Deg → Share := by
  first | exact @_root_.GlobalTheory.CovTop.ShareRowsNef.share_of_deg | exact _root_.GlobalTheory.CovTop.ShareRowsNef.share_of_deg | (intros; apply _root_.GlobalTheory.CovTop.ShareRowsNef.share_of_deg <;> assumption)
end
