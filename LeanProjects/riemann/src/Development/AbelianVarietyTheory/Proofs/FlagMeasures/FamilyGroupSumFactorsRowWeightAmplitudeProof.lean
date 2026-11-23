import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstT
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalAmplitudeEqLocalAmplitudesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowDoubleCosetSumNormSqBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagTermInvariantsConstOnRationalDoubleCosetStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalIntegralsTermsOneDoubleCosetStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalCoordinatesRationalFlagPairStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermMovesToBaseFramesUpToUnitriangularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubleCosetEqIffIsometryUnipotentTranslateStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowTermAmplitudeEqMassMulPhaseStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScaleNormalisedLocalReadingStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRelevantPairStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsAtPointOfRelevantTermRelevantFiniteStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericFamilyClassesDetermineRowsStatement

noncomputable section

open scoped Classical Pointwise
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.FamDefs Formalism.MainNotions.S.LocNG GlobalTheory.HL GlobalTheory.LocOver GlobalTheory.SnFam

namespace GlobalTheory.FamilyNormRational

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem toPts_inj' {K : Type} [Zero K] {i : ℕ} (p q : Point K (i + 1)) (h : toPts p = toPts q) : p = q := by
  have hb : p.1.map Prod.snd = q.1.map Prod.snd := congrArg (fun x => x.1.blocks) h
  have hl : p.1.length = q.1.length := by simpa using congrArg List.length hb
  have hv : ∀ k (hk : k < p.1.length) (hk' : k < q.1.length), (p.1[k]).1 = (q.1[k]).1 := by
    intro k hk hk'
    have key := congrArg (fun x : (Σ c : Composition (i + 1), (Fin c.length → K)) =>
      if hk : k < x.1.length then x.2 ⟨k, hk⟩ else 0) h
    have e1 : k < (toPts p).1.length := by simpa [toPts, Composition.length] using hk
    have e2 : k < (toPts q).1.length := by simpa [toPts, Composition.length] using hk'
    simp only [dif_pos e1, dif_pos e2] at key
    simpa [toPts] using key
  apply Subtype.ext
  apply List.ext_getElem hl
  intro k hk hk'
  have hs := congrArg (fun l => l[k]?) hb
  simp only [List.getElem?_map, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk', Option.map_some,
    Option.some.injEq] at hs
  exact Prod.ext (hv k hk hk') hs

theorem one_mem_nRat {D : D7} {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F :=
  ⟨one_mem _, fun j x _ => by simp, fun x _ => by simp⟩

theorem squaredGroupSum_classDoubleCoset_eq_rowWeight : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k →
    ConcTie X Y → ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ s : X.B.I.Ginf → NNReal, (∀ γ, 0 < s γ) →
    (∀ w : Point D.host.E (D.R.rS + 1), (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) →
      (s (Formalism.L2.SG.RealObj.gamW X u u' w) : ℝ) = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹)) →
    ∀ (K : Type) (S : Prop → Prop) (TS : Set (TauC Y u u')) (cls : TauC Y u u' → K), FamQ Y u u' S TS cls →
    ∀ γ : PN.Pts D.host.E D.R.rS, HasPt Y u u' TS γ →
    ∀ Fm : LocFam (zOf Y) K (NuC D), FamTie TS cls (nmlOf Y u u') γ Fm →
    ∀ (c : K) (n : NuC D), a2F Y u u' TS cls (sc s ν) c γ n = a2W Fm.toL (ampQ S Fm.toL) c n := by
  intro D X Y u u' hSt hk hCT ν hνP s hs0 hsw K S TS cls hFQ γ hγ Fm hFT c n
  obtain ⟨w, F00, F'0, F'1, hw, -, -, -, hZ, hbase, hOm, hgood, -, -, -, -, hdat, -, -⟩ := hFT
  have hdc := hdat c n
  have hL : Fm.toL.dat c n = Fm.dat c n := rfl
  show ‖grpF Y u u' TS cls c γ n‖ ^ 2 / J2of Y u u' (sc s ν) γ = a2W Fm.toL (ampQ S Fm.toL) c n
  unfold a2W
  rw [hL]
  rcases hd : Fm.dat c n with _ | d
  · rw [hd] at hdc
    have h0 : grpF Y u u' TS cls c γ n = 0 := by
      unfold grpF
      have h0 : ∀ t, (TS ∩ {t | cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = n}).indicator (Y.tO u u').vec t = 0 := by
        intro t; apply Set.indicator_of_notMem; rintro ⟨h1, h2, h3, h4⟩; exact hdc ⟨t, h1, h2, h3, h4⟩
      simp [h0]
    simp [h0]
  · rw [hd] at hdc
    obtain ⟨⟨t0, ht0, hc0, hp0, hn0⟩, hall⟩ := hdc
    obtain ⟨hOv, hrw⟩ := hall t0 ht0 hc0 hp0 hn0
    obtain ⟨hTS, hCR, hRow⟩ := hFQ
    obtain ⟨t1, ht1, hv1, hp1⟩ := hγ
    have hGTS : ∀ t ∈ TS, t.G ≠ 0 := by
      intro t ht h0
      rw [hTS] at ht
      apply ht.1
      show Formalism.L2.SG.TermOp.Gt t = 0
      unfold Formalism.L2.SG.TermOp.Gt
      rw [if_pos h0]
    have hG1 := hGTS t1 ht1
    have hG0 := hGTS t0 ht0
    have hrel1 : t1.relevant := (GlobalTheory.T.nonGeneric_family_classes_determine_rows D X Y u u' hCT).2.2 t1 hv1
    obtain ⟨w1, hw1, hat1, -⟩ := GlobalTheory.T.terms_at_point_of_relevant_term_relevant_finite D X Y u u' t1 hG1 hrel1
    have hw1w : w1 = w := toPts_inj' _ _ (hw1.trans (hp1.trans hw.symm))
    subst hw1w
    have hatOf : ∀ t : TauC Y u u', ptPN t = γ → t.relevant ∧ t.toTerm.atPt w1 ∧ Formalism.L2.SG.PairVal.ptOf t.toTerm = w1 := by
      intro t ht
      obtain ⟨hr, hg, hcell⟩ := hat1 t (ht.trans hp1.symm)
      refine ⟨hr, ⟨(Quot.out t.toTerm.cls).1, ⟨(Quot.out t.toTerm.cls).2, Quot.out_eq _⟩, hg, hcell⟩, ?_⟩
      exact toPts_inj' _ _ (ht.trans hw.symm)
    obtain ⟨hrel0, hat0, hpt0⟩ := hatOf t0 hp0
    obtain ⟨-, hat1', hpt1⟩ := hatOf t1 hp1
    have hAtB : ∀ p, AtBase (zOf Y) p F00 F'0 (Tu D u) (Tu D u') (Fm.FP p) := fun p =>
      ⟨(hbase p).1, (hbase p).2.1, (hbase p).2.2.1, (hbase p).2.2.2⟩
    have hGv : Gval F00 F'0 ≠ 0 := by
      obtain ⟨-, hg0, hcell0⟩ := hat1 t0 (hp0.trans hp1.symm)
      have hcell00 : IsInCell (ZhatOM (ZhatL F00 F'0)) w1 :=
        ⟨1, 1, fun i j => ⟨fun h => Matrix.one_apply_ne (ne_of_lt h), fun h => h ▸ Matrix.one_apply_eq i⟩,
          fun i j => ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), fun h => h ▸ Matrix.one_apply_eq i⟩,
          by rw [hZ, Matrix.one_mul, Matrix.mul_one]⟩
      have e1 := Formalism.L2.SG.WConst.gPoint_eq_gval F00 F'0 w1 hcell00
      have e2 := Formalism.L2.SG.WConst.gPoint_eq_gval (T := Tu D u) (T' := Tu D u') (lf D (X.Fu u)) (Quot.out t0.toTerm.cls).1
        w1 hcell0
      rw [← e1, e2]
      exact hg0
    have hBase : ∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (Fm.FP p) ∧
        (Fm.FP p).RelG (LocNG.theta (Y.M p)) := fun p =>
      ⟨hAtB p, (GlobalTheory.T.localisedBaseFrames_relevantPair D (zOf Y) u u' w1 F00 F'0 hZ hGv p).2 _ (hAtB p)⟩
    obtain ⟨G, ⟨cc⟩⟩ := GlobalTheory.T.exists_global_coordinates_rational_flagPair D X Y u u' hSt w1 F00 F'0 Fm.FP hZ hGv hBase
    obtain ⟨ρ, U, U', hmv⟩ := GlobalTheory.T.term_moves_to_baseFrames_up_to_unitriangular D X Y u u' hSt w1 F00 F'0 Fm.FP hZ hGv hBase t0 hat0
    have hcore := GlobalTheory.T.row_doubleCoset_sum_norm_sq_bound D X Y u u' hSt hk w1 F00 F'0 Fm.FP hZ hGv hBase G cc ν hνP t0 ρ U U' hmv hrel0 hpt0 S
    have hamp := GlobalTheory.T.globalAmplitude_eq_localAmplitudes D X Y u u' hSt hk w1 F00 F'0 Fm.FP hZ hGv hBase G cc t0 ρ U U' hmv Fm.R Fm.P Fm.Om
      (fun p => (d p).1) hgood hOm (fun p => hOv p.1 p.2) S
    have hset : (TS ∩ {t | cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = n}) =
        {t : TauC Y u u' | (Y.tO u u').rowOf t = (Y.tO u u').rowOf t0 ∧ nmlOf Y u u' t = nmlOf Y u u' t0 ∧
          S (¬ t.generic)} := by
      ext t
      constructor
      · rintro ⟨htS, hct, -, hnt⟩
        refine ⟨hRow t htS t0 ht0 (hct.trans hc0.symm), hnt.trans hn0.symm, ?_⟩
        have h2 := htS
        rw [hTS] at h2
        exact h2.2
      · rintro ⟨hr, hnm, hS⟩
        obtain ⟨nn, mm, hnn, hmm, hlin⟩ := (GlobalTheory.T.doubleCoset_eq_iff_isometry_unipotent_translate D X Y u u' hSt t0 t).1 hnm
        obtain ⟨-, hGeq, hpteq, -, -⟩ := GlobalTheory.T.flagTerm_invariants_const_on_rationalDoubleCoset D X Y u u' hSt t0 t nn mm hrel0 hG0 ⟨hnn, hmm, hlin⟩
        have htS : t ∈ TS := by
          rw [hTS]
          refine ⟨?_, hS⟩
          show Formalism.L2.SG.TermOp.Gt t ≠ 0
          unfold Formalism.L2.SG.TermOp.Gt
          rw [if_neg (hGeq ▸ hG0)]
          exact one_ne_zero
        refine ⟨htS, ((hCR t htS t0 ht0 hnm).2 hr).trans hc0, ?_, hnm.trans hn0⟩
        show toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm) = γ
        rw [hpteq]
        exact hp0
    have hrep : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w1 g :=
      (GlobalTheory.T.orbital_integrals_terms_one_doubleCoset D X Y u u' hSt ν hνP t0 hrel0 hG0 w1 hpt0.symm).1
    have hJ : J2of Y u u' (sc s ν) γ = (s (Formalism.L2.SG.RealObj.gamW X u u' w1) : ℝ) ^ 2 *
        ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w1)‖ ^ 2 := by
      unfold J2of
      have hex : ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = γ ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w' g :=
        ⟨w1, hw, hrep⟩
      rw [dif_pos hex]
      have hcw : hex.choose = w1 := toPts_inj' _ _ (hex.choose_spec.1.trans hw.symm)
      rw [hcw, Jw_sc, map_smul, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hJne : ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w1)‖ ≠ 0 := by
      intro h0
      obtain ⟨ρ1, U1, U1', hmv1⟩ := GlobalTheory.T.term_moves_to_baseFrames_up_to_unitriangular D X Y u u' hSt w1 F00 F'0 Fm.FP hZ hGv hBase t1 hat1'
      obtain ⟨T, hT, hamp1⟩ := GlobalTheory.T.rowTerm_amplitude_eq_mass_mul_phase D X Y u u' hSt hk w1 F00 F'0 Fm.FP hZ hGv hBase G cc ν hνP t1 ρ1 U1 U1'
        hmv1 hrel1 hpt1
      have he := hamp1 t1 1 1 rfl ⟨one_mem_nRat _, one_mem_nRat _, by simp⟩
      have hT0 : Formalism.L2.SG.PackageTie.hsEmb T = 0 := norm_eq_zero.1 (hT.trans h0)
      apply hv1
      show Formalism.L2.SG.TermOp.vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t1 = 0
      unfold Formalism.L2.SG.TermOp.vec
      rw [he, map_smul, hT0, smul_zero, smul_zero]
      ext q
      simp
    have hgi := hsw w1 hrep
    have hspos : (0 : ℝ) < s (Formalism.L2.SG.RealObj.gamW X u u' w1) := by exact_mod_cast hs0 _
    have hampeq : ‖G.amp (G.datOf (cc.lat ρ t0.lam)) (fun Γ => S (¬ G.Gen (G.datOf (cc.lat ρ t0.lam)) Γ))‖ =
        ‖ampQ S Fm.toL d‖ := by
      rw [hamp]; unfold ampQ
      congr 1
      refine Finset.sum_congr rfl (fun A _ => Finset.prod_congr rfl (fun p _ => ?_))
      split_ifs <;> first | rfl | (exfalso; tauto)
    have hgrp : grpF Y u u' TS cls c γ n = ∑' t : TauC Y u u', {t : TauC Y u u' | (Y.tO u u').rowOf t =
        (Y.tO u u').rowOf t0 ∧ nmlOf Y u u' t = nmlOf Y u u' t0 ∧ S (¬ t.generic)}.indicator (Y.tO u u').vec t := by
      unfold grpF; rw [hset]
    rw [hgrp, hcore, hJ, hampeq]
    show _ = Fm.rw c * ‖ampQ S Fm.toL d‖ ^ 2
    rw [hrw, ← hgi]
    have hJp : 0 < ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w1)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hJne)
    field_simp

theorem familyGroupSumFactorsRowWeightAmplitude : GlobalTheory.SnFam.FamilyGroupSumFactorsWeightAmplitude := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, le_rfl, 0, 0, fun C' Cl _ _ D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν => ?_⟩
  have hk := four_rank_add_seven_le_k hc
  obtain ⟨-, hSt, hCT⟩ := hc
  obtain ⟨s, hs1, hs0, hsle, hsw⟩ := GlobalTheory.T.exists_scale_normalised_localReading D X u u'
  refine ⟨s, hs1, hs0, fun γ => ?_, fun K S TS cls hFQ γ hγ Fm hFT c n =>
    squaredGroupSum_classDoubleCoset_eq_rowWeight D X Y u u' hSt hk hCT ν hν.2 s hs0 hsw K S TS cls hFQ γ hγ Fm hFT c n⟩
  have h1 : (s γ : ℝ) ≤ 1 := by exact_mod_cast hsle γ
  have h0 : (0 : ℝ) ≤ s γ := (s γ).2
  simp only [zero_mul, Real.rpow_zero]
  nlinarith

end GlobalTheory.FamilyNormRational
