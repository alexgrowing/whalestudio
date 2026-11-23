import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRootOfSUnitRatioUpToRootOfUnityClosureLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ListProdMapNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReferenceTupleFamilyPeriodEqPeriod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumRealEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamUnitaryHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataUnitShiftRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTotalConstantRatioOfFactorRatiosStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeFramePinsFiniteIntegralLawsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonzeroScalarsRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RankOneGramRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuadraticFamilyLevelIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueFamilyTopRowStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealEqualityOfColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainIdealIndexProductStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteLiftCommLevelPrimeOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyRowsColumnsValidStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawKernelLiftCombinationOfDefiniteClassDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastPeriodFactorizationOfClassDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawScalarFormsContinuousAutomorphicCentralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTupleKernelBackOfClassKernelDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastPeriodClassesGiveTailReadingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLiftExactConstantProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootOfUnityThetaTwistStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataLocalRelationStatement

set_option maxHeartbeats 4000000
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Fam.lawsLinks_of_geo_rows_cols : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row, (∀ t, (row t).Is) → (∀ t t', (row t).Same (row t')) → (∀ k : Cst a, ∃ col w₀ w F, GlobalTheory.AdForm.FamCol (a.fam row col) ∧ ColOut (row := row) (col := col) k w₀ w F) → ∃ col, (a.fam row col).RowOK ∧ LawsX (a.fam row col).t ∧ ChartZero (a.fam row col) ∧ LinkTail (a.fam row col) ∧ LinkComm (a.fam row col) ∧ RatioQ (a.fam row col) := by
  intro hDS hHC hSA B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT row hrow hsame hcol
  letI := a.fld; letI := a.val; letI := a.top; haveI := a.loc
  have hRow : ∀ col, (a.fam row col).RowOK := fun col => ⟨ha.meas, ha.last, ha.x, hrow, hsame⟩
  obtain ⟨col₀, -, -, -, -, -⟩ := hcol ⟨fun _ _ => 1, fun _ => ⟨0, Fin.elim0, Fin.elim0⟩, 0, 0, 0, 0⟩
  have hcIs : (commOf (pk W) u a.g).Is := (GlobalTheory.T.family_rows_columns_valid hDS hHC W u hW.pk (a.fam row col₀) (hRow col₀)).1
  obtain ⟨ε, op, r, e, cG, hr, hcG, hkap, hvIs, hall⟩ :=
    GlobalTheory.T.seeSaw_latticeFramePins_finiteIntegralLaws _ _ a.v a.k a.ι a.o a.n a.G hcIs ha.last ha.vis ha.shape ha.gpin
  obtain ⟨s, hs, hζ⟩ := GlobalTheory.T.nonzero_scalars_roots_of_unity _ _ _ _ _ _ _ _ _ W u (a.fam row col₀) hW.pk (hRow col₀) a.v ha.vis
    (ha.tie row col₀).1 a.n a.G a.pl ha.gpin (ha.tie row col₀).2
  choose ζ hζu hζv using hζ
  let k : Cst a := ⟨ε, op, r, e, cG, fun t j => s j * ζ t j⟩
  obtain ⟨col, w₀, w, F, hFC, hCO⟩ := hcol k
  have hQ : ∀ t p, p ∈ (w t).Q ↔ ∃ PP ∈ (pk W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F) := by
    intro t p
    rw [(hCO.same t).1, (hCO.pins t).places p]
    obtain ⟨pl, hpl⟩ := (hCO.lev t).places
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(pl i).1, (pl i).2, (hpl i).2⟩
    · rintro ⟨PP, hPP, rfl⟩
      exact ⟨pl.symm ⟨PP, hPP⟩, by rw [(hpl _).2, Equiv.apply_symm_apply]⟩
  have hVf : ∀ t, VfAt (a.fam row col) a.v (w t) (k.sc t) := by
    intro t
    let w' : VTup ((a.fam row col₀).t t) := ⟨(w₀ t).Q, 0, (w₀ t).eQ, (w₀ t).eQT, fun _ _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ _ => ∅,
      fun _ => ∅, ∅, 0, 0⟩
    have h1 := hζv t w' (fun p => by rw [← (hCO.same t).1]; exact hQ t p)
      (fun j => ⟨(hCO.atQ t j).1, (hCO.atQ t j).2.1⟩) (hCO.vec t)
    obtain ⟨-, he, heT, -⟩ := hCO.same t
    refine ⟨fun j hj P b hb b' hb' => ?_, fun j h P => ?_⟩
    · rw [he]; exact h1.1 j hj P b hb b' hb'
    · rw [heT]; exact h1.2 j h P
  have hIs := GlobalTheory.T.family_rows_columns_valid hDS hHC W u hW.pk (a.fam row col) (hRow col)
  have htIs : ∀ t, ((a.fam row col).t t).Is := hIs.2 hCO.ok
  have hweil := fun t => GlobalTheory.T.family_chars_weilOK_unramified W u hW.pk (a.fam row col) a.v (hRow col) hCO.ok (ha.tie row col).1
    (fun j h => ⟨ha.shape.pre.line.1, ha.shape.pre.tau j h⟩) t (w t) (hQ t)
  have hchars : ∀ t i, (a.G i).Chars ((a.fam row col).t t) := fun t => (hweil t).2.2.2.2.2.2 a.n a.G a.pl (ha.tie row col).2
  have hrowt := fun t => GlobalTheory.T.quadratic_family_level_identity _ _ _ _ _ _ _ _ _ W u (a.fam row col) hW.pk (hRow col) a.v ha.vis (ha.tie row col).1 a.n a.G a.pl
    ha.gpin (ha.tie row col).2 t (w₀ t) (F t) (htIs t) (hCO.pins t) (hCO.lev t) (hchars t)
  have hVF : ∀ t, VForm k.v (w t) := by
    intro t
    obtain ⟨hsQ, he, heT, -, hFY, hFT⟩ := hCO.same t
    have hw := hweil t
    have hrw := hrowt t
    have htie := (ha.tie row col).1
    obtain ⟨S₀, hS⟩ := hCO.read t
    refine ⟨hw.2.2.2.2.1, hw.2.2.2.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrw.2.1⟩
    · intro j hj P b hb b' hb'
      rw [hCO.sc t]; exact (hVf t).1 j hj P b hb b' hb'
    · intro j h P
      rw [hCO.sc t]; exact (hVf t).2 j h P
    · intro j
      have := hCO.atQ t j
      rw [← hsQ, ← he, ← heT] at this
      exact this
    · intro j α
      obtain ⟨h1, h2⟩ := hCO.e t j α
      have hb : k.v.b j = a.g.b j := htie.b j
      refine ⟨by rw [hb]; exact h1, fun g hg => ?_⟩
      rw [hsQ]; exact h2 g hg
    · intro n h β
      obtain ⟨h1, h2⟩ := hCO.eT t n h β
      have hb : k.v.bT = a.g.bT := htie.bT.1
      refine ⟨by rw [hb]; exact h1, fun g hg => ?_⟩
      rw [hsQ]; exact h2 g hg
    · exact hCO.dd t
    · intro j hj ψ hψ α y
      refine ⟨?_, hCO.FX t j hj ψ hψ α y, hS.S j hj ψ hψ α y⟩
      show _ ∈ a.v.RamAd j
      rw [ha.shape.ram j]; exact hS.ram j (by omega) ψ hψ α y
    · intro j hj G x b hb
      obtain ⟨h1, h2⟩ := hrw.1 j hj G x b hb
      refine ⟨?_, fun κ hκ => h2 κ ?_⟩
      · rw [hFY]; exact ((hCO.FY t j _).2 h1)
      · have hoff : offP k.v (w t) = offP a.v (w₀ t) := by
          funext p
          show (p ∉ a.v.gP ∧ p ∉ (w t).Q) = (p ∉ a.v.gP ∧ p ∉ (w₀ t).Q)
          rw [hsQ]
        rw [hoff] at hκ; exact hκ
    · intro G x
      rw [hFT]; exact hCO.FT t _
  obtain ⟨hloc, hval, hlast⟩ := hall W.P.T (a.fam row col).t w fun t => ⟨htIs t, hVF t, (hweil t).1, (hrowt t).2.2, (hweil t).2.1,
    (hweil t).2.2.2.1, hchars t, (hCO.laws t).1, (hCO.laws t).2.1, (hCO.laws t).2.2, hCO.cT t, hCO.cv t⟩
  have hcls : ClsPinD (a.fam row col).t := GlobalTheory.T.true_family_top_row W u (a.fam row col) hW.tr hW.tw ha.top (hRow col) hFC
  have hlaws : LawsX (a.fam row col).t := ⟨hIs.1, htIs, hloc, GlobalTheory.T.real_equality_of_columns W u hW.pk (a.fam row col) hCO.ok, hval, hlast,
    GlobalTheory.T.seeSawKernelLiftCombination_of_definiteClassData _ _ _ _ hIs.1 htIs hcls, GlobalTheory.T.seeSawLastPeriodFactorization_of_classData _ _ _ _ hIs.1 htIs hcls, GlobalTheory.T.seeSaw_scalarForms_continuous_automorphic_central _ _ _ _ hIs.1 htIs hcls⟩
  have hheq : ∀ t, W.P.I.tup t = (I.rec7 l Z).what₂.mu0 → ∀ φ, HEq (col0 (a.fam row col) t φ) ((I.rec7 l Z).eMu u φ).1 := by
    intro t ht φ
    show HEq ((I.rec7 l Z).e0Tw u (W.P.I.tup t) _) _
    rw [ht]
    exact heq_of_eq (GlobalTheory.Mem.Col2.TC.stepZeroTwist_reference_tuple_eq_id l u _)
  refine ⟨col, hRow col, hlaws, hCO.zero, GlobalTheory.MiTop.linkTail_of_topReadAt W u (a.fam row col) ha.top hheq, ?_, ?_⟩
  · obtain ⟨ρ, hρ, hA⟩ := hcls
    choose S₀ hS₀ using hCO.read
    have hsh : ShapeOff k.v a.o := by
      have hs := ha.shape
      have hp := hs.pre
      exact ⟨⟨hp.nodup, hp.all, hp.inj, hp.tP, hp.char, hp.latT, hp.line, hp.tau, hp.lam, hp.normT, hp.topT⟩,
        fun x => ⟨(hs.good x).bf, (hs.good x).fb⟩, fun x hx => ⟨(hs.split x hx).core, (hs.split x hx).top⟩, hs.glued, hs.rep,
        hs.ram⟩
    have hne : ∀ {S : ℕ → Prop} {x y : ℂ}, UnitRatio S x y → x ≠ 0 := fun h => ((GlobalTheory.Fam.unitRatio_laws _).2.1 _ _ _ _ h h).2.2
    refine GlobalTheory.T.type_data_unit_shift_relation W u (a.fam row col) a.k a.ι a.o ε S₀ (GlobalTheory.FinPl.RamUnit.ramUnitary_holds _) hIs.1
      (fun t => ⟨htIs t, ?_, ?_, ?_, hS₀ t⟩) ha.shape.pre.nodup ha.shape.pre.all ha.shape.pre.inj ?_ ?_ ?_
    · obtain ⟨⟨A, hAI⟩, -⟩ := hA t
      exact GlobalTheory.T.seeSawTuple_kernelBack_of_classKernelData _ _ _ ρ A hIs.1 (htIs t) hρ hAI fun j hj => hne (hCO.cK t j hj)
    · obtain ⟨-, A, hAI⟩ := hA t
      exact GlobalTheory.T.lastPeriodClasses_give_tailReading _ _ _ ρ A hAI (hne (hCO.cP t))
    · exact GlobalTheory.T.definiteLift_comm_levelPrimeOperators _ _ a.k a.ι k.v a.o _ (w t) (GlobalTheory.T.splitLiftExactConstant_proof _) hIs.1 (htIs t) hvIs (hVF t) hsh
        (GlobalTheory.T.type_data_local_relation W u hW.pk (a.fam row col) a.v a.k a.ι a.o (hRow col) hCO.ok ha.vis (ha.tie row col).1 ha.shape t)
    · intro t
      obtain ⟨α₀, -⟩ := hCO.zero t
      exact ⟨α₀⟩
    · intro t φ
      obtain ⟨α₀, hα, -, h3, -⟩ := hCO.zero t
      exact ⟨(h3 φ).1, fun α y => by rw [hα α]; exact (h3 φ).2 y⟩
    · intro t
      obtain ⟨α₀, -, -, -, h4⟩ := hCO.zero t
      exact h4
  · intro n hn t
    have hsc : ∀ tt j, j < (I.rec7 l Z).R.m → UnitRatio (qPrime W tt) ((w tt).sc j) ((w W.P.A3.A.μ0).sc j) ∧
        UnitRatio (qPrime W tt) (((a.fam row col).t tt).cK j) (((a.fam row col).t W.P.A3.A.μ0).cK j) := by
      intro tt j hj
      refine ⟨?_, hCO.cK tt j hj⟩
      rw [hCO.sc tt, hCO.sc W.P.A3.A.μ0]
      obtain ⟨n₁, hn₁, e₁⟩ := hζu tt j
      obtain ⟨n₂, hn₂, e₂⟩ := hζu W.P.A3.A.μ0 j
      have hz : ζ W.P.A3.A.μ0 j ≠ 0 := fun h0 => by rw [h0, zero_pow hn₂.ne'] at e₂; exact zero_ne_one e₂
      refine (GlobalTheory.Fam.unitRatio_laws _).2.2.1 _ _ (n₁ * n₂) (mul_ne_zero (hs j) hz) (Nat.mul_pos hn₁ hn₂) ?_
      show (s j * ζ tt j) ^ (n₁ * n₂) = (s j * ζ W.P.A3.A.μ0 j) ^ (n₁ * n₂)
      rw [mul_pow, mul_pow, pow_mul (ζ tt j), e₁, mul_comm n₁ n₂, pow_mul (ζ W.P.A3.A.μ0 j), e₂, one_pow, one_pow]
    have hcI : ∀ tt j, j < (I.rec7 l Z).R.m → ((a.fam row col).t tt).cI j ≠ 0 := fun tt j hj =>
      GlobalTheory.Fam.GeoMeas.cIOf_ne_zero (lvP W) ha.meas tt j hj
    have hci := fun tt => GlobalTheory.T.chain_ideal_index_product _ _ _ _ _ _ _ _ _ W u (a.fam row col) hW.pk (hRow col) a.v ha.vis (ha.tie row col).1 tt
      (w₀ tt) (F tt) (hCO.pins tt) (hCO.lev tt)
    have hq : ∀ tt j ρ, j + 2 * ρ + 2 = (I.rec7 l Z).R.m → (w tt).cQ j / (((a.fam row col).t tt).cI j * ((a.fam row col).t tt).cI (j + 1)) =
        (((a.fam row col).t W.P.A3.A.μ0).cI j * ((a.fam row col).t W.P.A3.A.μ0).cI (j + 1))⁻¹ := by
      intro tt j ρ h
      rw [(hCO.same tt).2.2.2.1, (hCO.pins tt).cQ j (by omega), ← hci tt j (by omega), ← hci tt (j + 1) (by omega),
        Finset.prod_inv_distrib, Finset.prod_mul_distrib, div_eq_mul_inv, ← mul_inv]
      congr 1
      ring
    have hct : ∀ tt j ρ, j + 2 * ρ + 2 = (I.rec7 l Z).R.m → UnitRatio (qPrime W tt) ((w tt).cT j) ((w W.P.A3.A.μ0).cT j) ∧
        UnitRatio (qPrime W tt) ((w tt).cQ j / (((a.fam row col).t tt).cI j * ((a.fam row col).t tt).cI (j + 1)))
          ((w W.P.A3.A.μ0).cQ j / (((a.fam row col).t W.P.A3.A.μ0).cI j * ((a.fam row col).t W.P.A3.A.μ0).cI (j + 1))) := by
      intro tt j ρ h
      refine ⟨?_, ?_⟩
      · rw [hCO.cT tt j ρ h, hCO.cT W.P.A3.A.μ0 j ρ h, ((hrow tt).sBF j ρ h).2.2.2, ((hrow W.P.A3.A.μ0).sBF j ρ h).2.2.2]
        exact GlobalTheory.SeeSaw.mono_unitRatio _ _ a.k a.ι a.o (r j) (e j) _ _ _ (hr j)
          ((GlobalTheory.T.root_of_unity_theta_twist _ _ _ _ _ _ _ _ _ W u (a.fam row col) hW.pk (hRow col) tt).choose_spec.2.2.2 (j + 1))
      · rw [hq tt j ρ h, hq W.P.A3.A.μ0 j ρ h]
        exact (GlobalTheory.Fam.unitRatio_laws _).1 _ (inv_ne_zero (mul_ne_zero (hcI _ j (by omega)) (hcI _ (j + 1) (by omega))))
    obtain ⟨h1, -, h3⟩ := GlobalTheory.T.seeSaw_totalConstant_ratio_of_factor_ratios _ _ k.v W.P.T (a.fam row col).t w (qPrime W) W.P.A3.A.μ0 htIs hCO.cv hkap hcG hsc hct
      hCO.cP n hn t
    exact ⟨h1, h3⟩
