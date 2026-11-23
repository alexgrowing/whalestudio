import Formalism.SharpRestriction.GrowthBounds.PlaneCountTheoremWithConstants
import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums
import Formalism.SharpRestriction.GrowthBounds.InitialMinorTransposeMemHighestWeight
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree
import Formalism.LocalToGlobal.GroupLattices.FockModels.DualInclusionLattices
import Formalism.LocalToGlobal.GroupLattices.FockModels.LoBlockActComp
import Formalism.LocalToGlobal.GroupLattices.FockModels.MulMemRiemannRochSpaceAdd
import Formalism.LocalToGlobal.GroupLattices.FockModels.WeylDim
import Formalism.LocalToGlobal.GroupLattices.FockModels.Cartan
import Formalism.SharpRestriction.GrowthBounds.JointsLit
import Formalism.SharpRestriction.GrowthBounds.SizesAtRecord
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PrvAndKernelCommutationUpToUnitsOfRests
import Formalism.LocalToGlobal.GroupLattices.FockModels.LPBase
import Formalism.LocalToGlobal.GroupLattices.FockModels.OperatorsPreserveLattices
import Formalism.LocalToGlobal.GroupLattices.FockModels.Sandwich
import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.LetterWtAnti
import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideFinal
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PositivityConditionHolds
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NpDescFOfValRatF
import Formalism.SharpRestriction.GrowthBounds.TruncatedChains
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.OrbitSumStabilizer
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StmtNumFEx
import Formalism.SharpRestriction.GrowthBounds.FockGramWindow
import Formalism.SharpRestriction.GrowthBounds.WittIdentPI
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials
import Formalism.SharpRestriction.GrowthBounds.AevalValuation

noncomputable section

namespace Formalism.L2.G

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G

structure Loc : Prop where

  p14R : ∀ D : D7, SecondTheoremReduced D

theorem extremal_projector_tools_of_loc (h : Loc) : ExtremalProjectorTools where
  extremalProjectorAlt := ExtremalProjector.extremal_projector_statement

theorem local_model_results (h : Loc) : Loc6 where
  p14R := h.p14R
  p39B := SelectionLemmas.Pf.secondPartClosed
  rationalPlanesClauseThree := Joints.Lit.weyl_dimension_formula_index_sets
  rationalPlanesClauseFour := Joints.Lit.branching_rule_count_form
  rationalPlanesClauseFive := Joints.Lit.pieri_rule_count_form
  dualInclusionLattices := Model.dualInclusionLattices
  bePerfect := Model.bePerfect
  lpOneEvery := Model.lPOneEvery
  flatTop := Model.flatTop
  dualHeightBasis := Model.dualHeightBasis
  hlSpans := Model.hlSpans
  testSide := Model.testSide
  wittIdent := WittPI.wittIdentity_holds
  criterionClauseElevenB := Joints.joint_types_corollary_sentences
  criterionClauseTwentyTwo := Joints.coarse_units_lemma
  criterionClauseThirtyFive := Model.fewBadOrbits
  criterionClauseThirtySix := Model.products_sections_integral

theorem local_flatness_results (h : Loc) : Loc8 where
  p13B := flipOneThree.Pf.theorem_I_closed_form_holds
  p13A := GramWindowAlt.theorem_A_closed_form_holds
  p15 := ColumnSystems.Pf.extendedClosedForm
  windowClauseTwo := Model.gl_branching_dimension
  windowClauseThree := Model.weyl_dual_weight_admissible
  lWeylV := Model.weylV_proved
  tFlatHH := Model.flatHH
  tCartanDomain := Model.cartanDomain_proved
  tCartanOnto := Model.cartanOnto_proved
  tKP2 := Joints.saturated_restriction_holds
  tKP3 := Joints.restriction_dimension_holds
  tRES := CountingStatementReduction.residue_division_transfer

theorem packet_statement_closed (𝒞 : FamClass) : Closed 𝒞 fun Fm _ => AuxBlock8.KudlaFamilyStatement Fm :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => AuxBlock8.Pf.stmtF Fm⟩⟩

def LocalDataSystem {D : D7} {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (low : D.what₂.Word → D.what₂.places.Pl → ℝ) : Prop :=
  ∀ hT : GatTies D, LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ∃ (_ : Fact (D.what₂.places.resChar w).Prime) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _)
      (dG_spec : _) (om : _) (Y5 : FormalGroupSystem.Pend (FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) (Y.Lv u w hg)
        (Y.Ch u w hg) std vp unif eO eO_spec dG dG_spec om)),
      (FormalGroupSystem.adm1 D → FormalGroupSystem.adm6 D _ Y5 → FormalGroupSystem.admitted D _ Y5) ∧
      ∃ Fn : Fin (D.gat u w hg).P.nV → ℕ → ℝ,
        (∀ v, v ∉ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg) → ∀ j < D.R.m, Y5.LowAt j v (Fn v (j + 1))) ∧
        low u w ≤ (∑ j ∈ Finset.Icc 1 D.R.m,
          ∑ v ∈ Finset.univ \ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg), Fn v j) -
            ∑ j ∈ Finset.range D.R.m, (dG j : ℝ)

theorem system_of_local_data {D : D7} {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (low : D.what₂.Word → D.what₂.places.Pl → ℝ)
    (h : LocalDataSystem X Y low) : LocalSystemCompletion X Y low := by
  intro hT hLT u w hg
  obtain ⟨hf, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hadm, Fn, hFn, hlow⟩ := h hT hLT u w hg
  exact ⟨hf, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5,
    hadm (Formalism.MainNotions.FormalGroupSystem.Pf.positivity_condition_holds D) (Formalism.L2.G.Pend.up_down_adjoint D _ Y5), Fn, hFn, hlow⟩

theorem hypIAt_ev {eps : ℝ} (Fm : FamP eps) (hLa : 0 < Fm.GK.La) (hCN : CornerGLContinuity.FamilyWindowLogBound Fm) :
    Ev Fm fun x i => Joints.HypIAt (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK := by
  obtain ⟨i0⟩ := Fm.Ix_zero
  have heps : 0 < eps := by
    have := (Fm.L 0 i0).sc.eps_pos
    rwa [Fm.L_eps] at this
  obtain ⟨C31, _, h1⟩ := TopChoiceBounds.family_uniform_constant_holds Fm
  have h1' : Ev Fm fun x i => AuxBlock8.adm1 (Fm.D x i) (Fm.L x i) (Fm.Gx x i) C31 := h1
  have h4 : Ev Fm fun x i => AuxBlock8.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) Fm.GK := TopChoiceBounds.family_band_ratio_statement Fm hCN
  have h5 := family_sizes_bound Fm hLa (eps / 48) (by positivity)
  have hx31 : Ev Fm fun x i => CornerGLContinuity.LargeScaleConditions (Fm.D x i) (Fm.L x i) := TopChoiceBounds.family_large_scale_conditions_hold Fm
  obtain ⟨xa, hA⟩ := Filter.eventually_atTop.1 ((AuxBlock8.Pf.numMean_ev eps Fm.GK Fm.GK_nonneg 0 le_rfl).and
    (AuxBlock8.Pf.restHypI_ev eps Fm.GK Fm.GK_nonneg 0 C31))
  obtain ⟨x0, h⟩ := ((((h1'.and h4).and h5).and hx31).and (eventually_sizes_admitted Fm)).and (Ev.x1 Fm)
  refine ⟨max x0 xa, fun x hx i => ?_⟩
  obtain ⟨⟨⟨⟨⟨a1, a4⟩, a5⟩, a31⟩, aSz⟩, hx1⟩ := h x (le_trans (le_max_left _ _) hx) i
  obtain ⟨hNM, hRH⟩ := hA x (le_trans (le_max_right _ _) hx)
  have hxx := Fm.L_x x i hx1
  have hee := Fm.L_eps x i
  have NM := hNM (Fm.D x i) (Fm.L x i) hxx hee aSz.1 a5
  have ZetaZeros := hRH (Fm.D x i) (Fm.L x i) (Fm.Gx x i) hxx hee aSz a5 a4 a1 NM
  obtain ⟨w⟩ := exists_place (Fm.D x i)
  obtain ⟨_, _, _, _, _, _, hLaG⟩ := Fm.fills x hx1 i w
  intro p hc hp0 t0 ht0
  exact ⟨a31.1, a31.2.2 _ hc.2.2.2.1, ZetaZeros p hc hp0 t0 ht0, windows_of Fm.GK (Fm.params x hx1 i) hLaG p t0⟩

structure Fam {eps : ℝ} (Fm : FamP eps) : Prop where

  gatE : Ev Fm fun x i => TrivialStabiliserFiniteClasses (Fm.D x i)

  stdSub : Ev Fm fun x i => Joints.StdSubAt (Fm.D x i)

  localSystemLowTerm : Ev Fm fun x i => LocalDataSystem (Fm.Gx x i) (Fm.Gy x i) (AuxBlock8.lowU (Fm.D x i))

  localSystemSizeLowTerm : Ev Fm fun x i => LocalDataSystem (Fm.Gx x i) (Fm.Gy x i) (lowFE (Fm.L x i))

theorem family_satisfies_ties {eps : ℝ} (Fm : FamP eps) (h : Fam Fm) (hCN : CornerGLContinuity.FamilyWindowLogBound Fm) (hLa : 0 < Fm.GK.La) : Fam1 Fm where
  p6G := ⟨0, fun x _ i => FormalGroupSystem.Pf.stmt6G _ _ _ _ _⟩
  p05 := FormalGroupSystem.Pf.stmtF_proved Fm
  gatE := h.gatE
  gatY := ⟨0, fun x _ i u w hg => Model.operators_preserve_lattices _ _⟩
  stdSub := h.stdSub
  lpBC := Model.lpBaseChange
  hypII := Joints.hypIIAt_fam Fm hCN
  model := ⟨0, fun x _ i => Model.modelSandwichG_of_ties _ (Fm.gatT x i)⟩
  localSystemLowTerm := by
    obtain ⟨x0, h0⟩ := h.localSystemLowTerm
    exact ⟨x0, fun x hx i => system_of_local_data _ _ _ (h0 x hx i)⟩
  localSystemSizeLowTerm := by
    obtain ⟨x0, h0⟩ := h.localSystemSizeLowTerm
    exact ⟨x0, fun x hx i => system_of_local_data _ _ _ (h0 x hx i)⟩
  hypI := hypIAt_ev Fm hLa hCN

theorem link_of_descent_closed (𝒞 : FamClass) (h : Loc) (hN : FormalGroupSystem.NumericalComparisonUniform) (hf : Closed 𝒞 fun Fm _ => Fam Fm)
    (h2 : Closed 𝒞 fun Fm _ => Adm2F Fm) (hd : Closed 𝒞 fun Fm _ => NPDescF Fm) :
    Closed 𝒞 fun Fm _ => LinkG Fm :=
  link_of_closed_families 𝒞 (extremal_projector_tools_of_loc h) (local_model_results h) (local_flatness_results h) hN (packet_statement_closed 𝒞) (((hf.and (TopChoiceBounds.family_log_bound_closed 𝒞)).and (signs_closed 𝒞)).imp fun Fm _ _ h => family_satisfies_ties Fm h.1.1 h.1.2 h.2.1) h2 hd

theorem link_of_numbers_proved (𝒞 : FamClass) (h : Loc) (hf : Closed 𝒞 fun Fm _ => Fam Fm)
    (h2 : Closed 𝒞 fun Fm _ => Adm2F Fm) (hd : Closed 𝒞 fun Fm _ => NPDescF Fm) :
    Closed 𝒞 fun Fm _ => LinkG Fm :=
  link_of_descent_closed 𝒞 h FormalGroupSystem.Pf.stmtNumE hf h2 hd

section NoKer

variable {D : D7} {L : SizeData₂ D}

def zeroCh (Y : LatInst D) : LatInst D where
  vOf := Y.vOf
  Fl := Y.Fl
  Lv := Y.Lv
  Ch := fun _ _ _ => ⟨fun _ => 0⟩
  Vram := Y.Vram

theorem chainK_zero {p : ℕ} {G : GAtP p} {Fl : Fills G} (Lv : Levels Fl) :
    ∀ m : ℕ, 1 ≤ m → ∀ F : Lv.Fm 0, (⟨fun _ => 0⟩ : Chain Lv).chainK m F = 0
  | 0, h, _ => absurd h (by omega)
  | n + 1, _, F => by simp [Chain.chainK]

theorem vKge_zero (Y : LatInst D) (hm : 1 ≤ D.R.m) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (F : (D.gat u w hg).Fn) (g : ℝ) :
    (zeroCh Y).vKge u w hg F g := by
  have h0 : ((zeroCh Y).Ch u w hg).chainK D.R.m F = 0 := chainK_zero _ D.R.m hm F
  unfold LatInst.vKge vGeLat
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (D.gat u w hg).O
  refine ⟨ϖ, hϖ, ?_⟩
  rw [h0]
  exact Submodule.zero_mem _

theorem admissible_family_no_kernel {eps : ℝ} (Fm : FamP eps)
    (h1 : Adm1F Fm) (h2 : Adm2F Fm) (h3 : Adm3F Fm) (h4 : Adm4F Fm) (h5 : Adm5F Fm) (h6 : Adm6F Fm) (h7 : Adm7F Fm)
    (h8 : Adm8F Fm) (h9 : Adm9F Fm)
    (hE : Ev Fm fun x i => TrivialStabiliserFiniteClasses (Fm.D x i)) (hY : Ev Fm fun x i => OperatorsPreserveLattices (Fm.D x i))
    (hLP : Ev Fm fun x i => CornerGLContinuity.OrbitLatticeBounds (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK)
    (hEp : Ev Fm fun x i => CornerGLContinuity.LatticeSandwich (Fm.D x i) (Fm.L x i) (Fm.Gx x i))
    (hd : NPDescF Fm) : AuxBlock8.AdmF Fm Fm.GK Fm.Gx (fun x i => zeroCh (Fm.Gy x i)) ∧
    Ev Fm fun x i => AuxBlock8.unitBoundAtTwistedPlaces (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (zeroCh (Fm.Gy x i)) Fm.GK ∧
      AuxBlock8.admG1 (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (zeroCh (Fm.Gy x i)) Fm.GK := by
  have hG1 : Ev Fm fun x i => AuxBlock8.unitBoundAtTwistedPlaces (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (zeroCh (Fm.Gy x i)) Fm.GK ∧
      AuxBlock8.admG1 (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (zeroCh (Fm.Gy x i)) Fm.GK := by
    obtain ⟨x0, h⟩ := ((((hE.and hY).and hLP).and hEp).and (eventually_large_scale_bound Fm)).and (Ev.x1 Fm)
    refine ⟨x0, fun x hx i => ?_⟩
    obtain ⟨⟨⟨⟨⟨hE, hY⟩, hLP⟩, hEp⟩, hB⟩, hx1⟩ := h x hx i
    have hU : AuxBlock8.unitBoundAtTwistedPlaces (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (zeroCh (Fm.Gy x i)) Fm.GK := by
      intro _ _ u w hg _ _ _ _ _ _ _
      exact vKge_zero _ hB.1 u w hg _ _
    have hS1 : CornerGLContinuity.ServiceLowerValuation (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (zeroCh (Fm.Gy x i)) Fm.GK := by
      intro _ _ u w hg _ _
      exact vKge_zero _ hB.1 u w hg _ _
    exact ⟨hU, TopChoiceBounds.gluing_statement_of_proof _ _ _ (TopChoiceBounds.gluing_statement_holds Fm.GK (Fm.Gx x i) (zeroCh (Fm.Gy x i))
      ⟨hU, stability_of_trivial_stabilisers hE, service_statement_of_stability _ _ _ (FormalGroupSystem.Pf.stmt6G _ _ _ _ _) hE hY, hLP, hEp,
        saturated_ramified_lattice _ (Fm.ex x hx1 i).cmp (Fm.ex x hx1 i).lat.vram, hB, hS1⟩).1⟩
  have hA : AuxBlock8.AdmF Fm Fm.GK Fm.Gx (fun x i => zeroCh (Fm.Gy x i)) := by
    obtain ⟨C31, hC31, h1⟩ := h1
    obtain ⟨Cm, hCm, h8⟩ := h8
    obtain ⟨Ce, hCe, h9⟩ := h9
    refine ⟨C31, Ce, Cm, hC31, hCe, hCm, fun δ hδ => ?_⟩
    obtain ⟨x0, h⟩ := ((((((((((h1.and h2).and h3).and h4).and (h5 δ hδ)).and h6).and h7).and h8).and h9).and
      hG1).and (eventually_sizes_admitted Fm))
    refine ⟨max x0 2, lt_of_lt_of_le one_lt_two (le_max_right _ _), fun x hx i => ?_⟩
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, aU, aG⟩, aS⟩ :=
      h x (le_trans (le_max_left _ _) hx) i
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, aU, aG, aS⟩
  exact ⟨hA, hG1⟩

theorem linkG_without_kernels {eps : ℝ} (Fm : FamP eps)
    (h1 : Adm1F Fm) (h2 : Adm2F Fm) (h3 : Adm3F Fm) (h4 : Adm4F Fm) (h5 : Adm5F Fm) (h6 : Adm6F Fm) (h7 : Adm7F Fm)
    (h8 : Adm8F Fm) (h9 : Adm9F Fm)
    (hE : Ev Fm fun x i => TrivialStabiliserFiniteClasses (Fm.D x i)) (hY : Ev Fm fun x i => OperatorsPreserveLattices (Fm.D x i))
    (hLP : Ev Fm fun x i => CornerGLContinuity.OrbitLatticeBounds (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK)
    (hEp : Ev Fm fun x i => CornerGLContinuity.LatticeSandwich (Fm.D x i) (Fm.L x i) (Fm.Gx x i))
    (hd : NPDescF Fm) : LinkG Fm := by
  obtain ⟨hA, hG1⟩ := admissible_family_no_kernel Fm h1 h2 h3 h4 h5 h6 h7 h8 h9 hE hY hLP hEp hd
  obtain ⟨C, δ, hδ, hP'⟩ := AuxBlock8.Pf.stmtF Fm Fm.GK Fm.GK_nonneg Fm.Gx _ hA
  have hP'' : Ev Fm fun x i => AuxBlock8.Conclusion₂ (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK C ((Fm.L x i).sc.b ^ δ x) := hP'
  obtain ⟨x0, h⟩ := (((((hP''.and hG1).and (servedGIdx_ev Fm)).and (svBound_ev Fm)).and (nuServed_ev Fm)).and
    (sizeDataLat_ev Fm hd)).and (Ev.x1 Fm)
  refine ⟨4 * |C| + 1, x0, δ, hδ, fun x hx i => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨hp, hg⟩, hs⟩, hv⟩, hi⟩, hf⟩, hx1⟩ := h x hx i
  exact linkG_at_of (Fm.Gx x i) (zeroCh (Fm.Gy x i)) Fm.GK Fm.GK_nonneg C _ (Fm.gatT x i) (Fm.fills x hx1 i)
    hf (Fm.supp_sat x hx1 i) (Fm.latTied x hx1 i) (Fm.nuDef x hx1 i) hp.1 hp.2.1 hp.2.2.2.2.1 hg.2 hs hv hi

theorem linkG_fam_noKer {eps : ℝ} (Fm : FamP eps) (h14 : SecondTheoremAtFamily Fm) (h13 : FirstTheoremAtFamily Fm)
    (hLa : 0 < Fm.GK.La) (hCe : 1 ≤ Fm.cX.Ce) (hCb : Ev Fm fun x i => CbLarge Fm.GK (Fm.L x i).sc)
    (hE : Ev Fm fun x i => TrivialStabiliserFiniteClasses (Fm.D x i)) (hS : Ev Fm fun x i => Joints.StdSubAt (Fm.D x i))
    (h2 : Adm2F Fm) (hd : NPDescF Fm) (hCN : CornerGLContinuity.FamilyWindowLogBound Fm) : LinkG Fm := by
  obtain ⟨C, hC0, a1, a2, a3, a4, a5, a6, hp14⟩ := h14
  obtain ⟨CH, C', b0, b1, b2, b3, b4, b5, b6, hp13⟩ := h13
  have h6 := family_second_bound_of_theorem Fm C hC0 a1 a2 a3 a4 a5 a6 hp14
  have h7 := family_kappa_bound Fm (kapIDefF Fm)
  have h8 := family_first_bound_of_theorem Fm CH C' (kapIDefF Fm) b0 b1 b2 b3 b4 b5 b6 hp13
  have hCe0 : 0 ≤ Fm.cX.Ce := le_trans zero_le_one hCe
  obtain ⟨C₅, h59⟩ := UnusedSlot33.field_lemmas_except_seven
  have hO : CornerGLContinuity.FamilyGlobalOrderEstimate Fm 100 := fun x i => (h59 (Fm.D x i) (Fm.L x i).sc).2.2.2.1
  have h9 : Adm9F Fm := by
    obtain ⟨x1, hx1⟩ := Ev.x1 Fm
    exact ⟨Fm.cX.Ce, hCe0, x1, fun x hx i => Joints.weyl_sandwich_of_factors _ _ _ Fm.cX.Ce hCe0 (Fm.ex x (hx1 x hx i) i).ep_def
      (Joints.weylSandwich_of_model _ (Model.modelSandwichG_of_ties _ (Fm.gatT x i)))
      (Joints.expBound_of _ _ _ Fm.cX.Ce hCe (Fm.ex x (hx1 x hx i) i).ep_def (Fm.params x (hx1 x hx i) i)
        (Fm.gatT x i))⟩
  have hLP : Ev Fm fun x i => CornerGLContinuity.OrbitLatticeBounds (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK := by
    obtain ⟨x0, h⟩ := ((((h6.and h7).and hS).and (hypIAt_ev Fm hLa hCN)).and
      (Joints.hypIIAt_fam Fm hCN)).and hCb
    exact ⟨x0, fun x hx i => Joints.linear_programming_input_of_hypotheses _ _ _ _ _ (h x hx i).1.1.1.1.1 (h x hx i).1.1.1.1.2
        (h x hx i).1.1.1.2 Model.lpBaseChange (h x hx i).1.1.2 (h x hx i).1.2
        (rho_le_rhoB _ _ _ Fm.GK_nonneg.2.1 (La_nonneg Fm.GK_nonneg.1 _) (h x hx i).2)⟩
  have hEp : Ev Fm fun x i => CornerGLContinuity.LatticeSandwich (Fm.D x i) (Fm.L x i) (Fm.Gx x i) := by
    obtain ⟨Ce, _, x0, h⟩ := id h9
    exact ⟨x0, fun x hx i => TopChoiceBounds.sandwich_of_exponent_clause _ Ce (Fm.gatT x i) (h x hx i)⟩
  exact linkG_without_kernels Fm (family_first_lemma Fm) h2 (family_orders_first_part Fm 100 (TopChoiceBounds.family_order_bound_holds Fm 100) hO)
    (family_orders_bound_of_lemma Fm (TopChoiceBounds.family_band_ratio_holds Fm) hCN) (family_sizes_bound Fm hLa) h6 h7 h8 h9 hE
    ⟨0, fun x _ i u w hg => Model.operators_preserve_lattices _ _⟩ hLP hEp hd

theorem link_of_local_closed (𝒞 : FamClass) (h : Loc)
    (hE : Closed 𝒞 fun Fm _ => Ev Fm fun x i => TrivialStabiliserFiniteClasses (Fm.D x i))
    (hS : Closed 𝒞 fun Fm _ => Ev Fm fun x i => Joints.StdSubAt (Fm.D x i))
    (h2 : Closed 𝒞 fun Fm _ => Adm2F Fm) (hd : Closed 𝒞 fun Fm _ => NPDescF Fm) :
    Closed 𝒞 fun Fm _ => LinkG Fm :=
  ((((((((((second_theorem_closed_form 𝒞 (second_theorem_absolute_constant (extremal_projector_tools_of_loc h) (local_model_results h))).and
    (first_theorem_closed_form 𝒞 (first_theorem_threshold_functions (extremal_projector_tools_of_loc h)
      (loc8All_of (extremal_projector_tools_of_loc h) (local_model_results h) (local_flatness_results h))))).and (signs_closed 𝒞)).and
    (ones_closed 𝒞)).and (cb_closed 𝒞)).and hE).and hS).and h2).and hd).and (TopChoiceBounds.family_log_bound_closed 𝒞)).imp
    fun Fm _ _ h => linkG_fam_noKer Fm h.1.1.1.1.1.1.1.1.1 h.1.1.1.1.1.1.1.1.2 h.1.1.1.1.1.1.1.2.1
      h.1.1.1.1.1.1.2.2.2 h.1.1.1.1.1.2 h.1.1.1.1.2 h.1.1.1.2 h.1.1.2 h.1.2 h.2

theorem loc_proved : Loc := by
  exact ⟨fun D => Formalism.MainNotions.G.criterion_restricted_of_closed D (Formalism.MainNotions.TraceSpectra.stmtE D)⟩

end NoKer

end Formalism.L2.G

end
