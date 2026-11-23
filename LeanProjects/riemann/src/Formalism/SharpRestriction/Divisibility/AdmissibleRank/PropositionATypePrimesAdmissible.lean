import Mathlib
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
import Formalism.SharpRestriction.Divisibility.FamilyThetaDenominatorValues
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Formalism.SharpRestriction.Divisibility.AdmissibleRank.NoBoundaryComponentOfAbelianAtGenericPoints
import Formalism.SharpRestriction.Divisibility.ChainOperators.CutDivD
import Formalism.SharpRestriction.Divisibility.ChainOperators.CutKapD
import Formalism.SharpRestriction.Divisibility.ChainOperators.RankInputBounds
import Formalism.SharpRestriction.Divisibility.ChainOperators.GeometricGenericity
import Formalism.SharpRestriction.Divisibility.IsotypicCorollary

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.MainNotions

section P18rec

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)

theorem integrality_admissible_of_inputs (h : ThetaNormsAndLinks.Conclusion1 D X) : LiftErrorLocal.adm1 D X := h

theorem height_admissible_of_inputs (h : ThetaNormsAndLinks.Conclusion2 D X) : LiftErrorLocal.adm2 D X := h

theorem jet_admissible_of_prismatic (h : ModuliIntegralCharts.LinkConditions D X.P6) : LiftErrorLocal.adm3 D X := h

theorem jet_admissible_of_jet_lattice (h : BoundaryLocalData.Conclusion5 D X.P6) : LiftErrorLocal.adm3 D X := h

theorem jet_function_admissible_of (CRd : ℝ) (h : ThetaNormsAndLinks.CoveringRadiusFunction D X CRd) : LiftErrorLocal.adm3b D X CRd := h

theorem theorem_zero_admissible_of (H : WeightAlgebra.KHyp) (C2 A2 CR CT : ℝ) (h : WeightAlgebra.Conclusion1 L X.W H C2 A2 CR CT) :
    LiftErrorLocal.ArchimedeanSignatureMatching D L X H C2 A2 CR CT := h

theorem galois_generic_admissible_of (h : ThetaNormsAndLinks.Conclusion5 D nch) : LiftErrorLocal.adm5 D nch := h

theorem share_admissible_of_inputs (h : ThetaNormsAndLinks.Conclusion6 D nch) : LiftErrorLocal.adm6 D nch := h

theorem lattice_ranks_admissible_of (h : ThetaNormsAndLinks.ShareLatticeRanks D nch) : LiftErrorLocal.TorsionSectionsReflex D nch := h

theorem link_admissible_of_inputs (h : ThetaNormsAndLinks.LinkConditions D X) : LiftErrorLocal.adm10 D X := h

theorem run_admissible_of_inputs (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) (h : ThetaNormsAndLinks.RunConditions D L X H C2 A2 CR CT CRd) :
    LiftErrorLocal.adm11 D L X H C2 A2 CR CT CRd := h

theorem lemma_one_two_A_hypotheses_of (h1 : ThetaNormsAndLinks.Conclusion1 D X) (h2 : ThetaNormsAndLinks.Conclusion2 D X) : LiftErrorLocal.AdmLA D X := ⟨h1, h2⟩

theorem lemma_B_hypotheses_of (CRd : ℝ) (h1 : ThetaNormsAndLinks.Conclusion1 D X) (h2 : ThetaNormsAndLinks.Conclusion2 D X) (h66 : ModuliIntegralCharts.LinkConditions D X.P6)
    (h3b : ThetaNormsAndLinks.CoveringRadiusFunction D X CRd) : LiftErrorLocal.AdmLB D X CRd := ⟨h1, h2, h66, h3b⟩

theorem proposition_C_hypotheses_of (h1 : ThetaNormsAndLinks.Conclusion1 D X) (h2 : ThetaNormsAndLinks.Conclusion2 D X) (a9 : LiftErrorLocal.adm9 D X) : LiftErrorLocal.AdmC D X := ⟨h1, h2, a9⟩

theorem division_admissible_of_inputs (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ)
    (h8 : ThetaNormsAndLinks.Conclusion₂ D L X H C2 A2 CR CT CRd) (h66 : ModuliIntegralCharts.LinkConditions D X.P6) (h08 : WeightAlgebra.Conclusion1 L X.W H C2 A2 CR CT)
    (a7 : LiftErrorLocal.adm7 D X) (a8 : LiftErrorLocal.adm8 D X) (a9 : LiftErrorLocal.adm9 D X) (a12 : LiftErrorLocal.adm12 D) :
    LiftErrorLocal.admitted D L X H C2 A2 CR CT CRd := by
  obtain ⟨p1, p2, p3b, p5, p6, p6b, -, p10, p11, -⟩ := h8
  exact ⟨p1, p2, h66, p3b, h08, p5, p6, p6b, a7, a8, a9, p10, p11, a12⟩

theorem proposition_A_hypotheses_of (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ)
    (h8 : ThetaNormsAndLinks.Conclusion₂ D L X H C2 A2 CR CT CRd) (h08 : WeightAlgebra.Conclusion1 L X.W H C2 A2 CR CT)
    (a7 : LiftErrorLocal.adm7 D X) (a8 : LiftErrorLocal.adm8 D X) (a12 : LiftErrorLocal.adm12 D) : LiftErrorLocal.AdmA D L X H C2 A2 CR CT CRd := by
  obtain ⟨-, -, p3b, p5, p6, p6b, -, p10, p11, -⟩ := h8
  exact ⟨p3b, h08, p5, p6, p6b, a7, a8, p10, p11, a12⟩

theorem local_cover_admissible_of (h : D.nd.LocsCover) : LiftErrorLocal.adm12 D := Formalism.MainNotions.N.locsCoverTw_of D h

end P18rec

section PDV08rec

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (Z : ThetaNormsAndLinks.Loc8 X)

theorem projector_integral_admissible_of (h : PDVN.ConjugationNormInvariance D) : ThetaNormsAndLinks.admA D := h

theorem sup_lattice_is_lattice_admissible (h : WeightFamilies.adm1 X.B) : ThetaNormsAndLinks.MLatticeCond D X := h

theorem transference_admissible_of (h : WeightFamilies.TransferenceTheoremCond) : ThetaNormsAndLinks.TransferenceTheoremCond := h

theorem twist_export_clause_of_twist_field (hW : ∀ i0 w, LiftErrorLocal.Over D i0 w → D.ntw.NonzeroIndexPlace (nch.twI w)) (h : IntegralHeckeForms.adm7 D X.I.E) :
    ThetaNormsAndLinks.admT4 D X := ⟨hW, h⟩

theorem trace_input_of_multiplicity_theorem (h4 : IsotypicCorollary.Stmt D) (C : NChoice D) : ThetaNormsAndLinks.EqualGoodMultiplicities D C := IsotypicCorollary.goodPartRank_of_corollary D h4 C

def ThetaNormLinkHypotheses (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop :=
  ThetaNormsAndLinks.admissible_unitary_of_inputs D X Z ∧ ThetaNormsAndLinks.SandwichExists D X ∧ ThetaNormsAndLinks.CharacterRankDiscriminant D X CRd ∧ ThetaNormsAndLinks.MirabolicIndexCond D ∧
    (ThetaNormsAndLinks.admR D nch ∧ ThetaNormsAndLinks.admG2 D ∧ ThetaNormsAndLinks.BadRowShareBound D L nch ∧ ThetaNormsAndLinks.EqualGoodMultiplicities D nch ∧ ThetaNormsAndLinks.SupLatticeGroupStable D) ∧ ThetaNormsAndLinks.SupSpansPsiPart D ∧
    (ThetaNormsAndLinks.AdditiveCharacterIntegrality D X ∧ ThetaNormsAndLinks.ScalingIntegrality D X ∧ ThetaNormsAndLinks.CrudeIntegrality D X ∧ ThetaNormsAndLinks.ThetaLevelPrimeIntegrality D X) ∧
    (ThetaNormsAndLinks.admT4 D X ∧ ThetaNormsAndLinks.NormDecompositionCond D X Z ∧ ThetaNormsAndLinks.ThetaKGroupStable D X Z ∧ ThetaNormsAndLinks.ThetaKEquivariantData D X Z ∧ ThetaNormsAndLinks.WeightGeneratorsInLattice D X) ∧
    (ThetaNormsAndLinks.RunColumnChoices D X ∧ ThetaNormsAndLinks.ScalarSizeConditions D L X H C2 A2 CR CT CRd ∧ ThetaNormsAndLinks.FurtherSizeConditions D L X H C2 A2 CR ∧ ThetaNormsAndLinks.GlobalScalarBounds D L X H ∧
      ThetaNormsAndLinks.RegularityOffTypePrimes D L X H)

theorem inputs_remaining_of_clauses (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) (P : ParameterChoice' D L) (hC6 : 6 ≤ CRd)
    (TN : Formalism.L2.NExpTied D) (h4 : IsotypicCorollary.Stmt D)
    (aI : ThetaNormsAndLinks.admissible_unitary_of_inputs D X Z) (aQ : ThetaNormsAndLinks.SandwichExists D X) (aGG : ThetaNormsAndLinks.MirabolicIndexCond D) (aR : ThetaNormsAndLinks.admR D nch) (aBad : ThetaNormsAndLinks.BadRowShareBound D L nch)
    (aGst : ThetaNormsAndLinks.SupLatticeGroupStable D) (aSp : ThetaNormsAndLinks.SupSpansPsiPart D) (aSg : ThetaNormsAndLinks.AdditiveCharacterIntegrality D X) (aSr : ThetaNormsAndLinks.ScalingIntegrality D X) (aSo : ThetaNormsAndLinks.CrudeIntegrality D X)
    (aSe : ThetaNormsAndLinks.ThetaLevelPrimeIntegrality D X) (aT4 : ThetaNormsAndLinks.admT4 D X) (aNN : ThetaNormsAndLinks.NormDecompositionCond D X Z) (aK : ThetaNormsAndLinks.ThetaKGroupStable D X Z) (aD : ThetaNormsAndLinks.ThetaKEquivariantData D X Z)
    (aW : ThetaNormsAndLinks.WeightGeneratorsInLattice D X) (aRc : ThetaNormsAndLinks.RunColumnChoices D X) (aRn : ThetaNormsAndLinks.ScalarSizeConditions D L X H C2 A2 CR CT CRd) (aR4 : ThetaNormsAndLinks.FurtherSizeConditions D L X H C2 A2 CR)
    (aRs : ThetaNormsAndLinks.GlobalScalarBounds D L X H) (aRd : ThetaNormsAndLinks.RegularityOffTypePrimes D L X H) :
    ThetaNormLinkHypotheses D L X Z H C2 A2 CR CT CRd :=
  ⟨aI, aQ, RankInputBounds.rank_input_holds D L P X CRd hC6, aGG,
    ⟨aR, GeometricGenericity.geometric_generic_of_layer_two D L P TN, aBad, IsotypicCorollary.goodPartRank_of_corollary D h4 nch, aGst⟩, aSp, ⟨aSg, aSr, aSo, aSe⟩,
    ⟨aT4, aNN, aK, aD, aW⟩, ⟨aRc, aRn, aR4, aRs, aRd⟩⟩

theorem inputs_admissible_of (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) (hM : WeightFamilies.adm1 X.B)
    (hB : WeightFamilies.TransferenceTheoremCond) (lv : ThetaNormLinkHypotheses D L X Z H C2 A2 CR CT CRd) : ThetaNormsAndLinks.admitted D L X Z H C2 A2 CR CT CRd := by
  obtain ⟨aI, aQ, aRk, aG, ⟨aR, aG2, aBad, aTR, aGst⟩, aSp, aS, ⟨aT4, aNN, aK, aD, aW⟩, aRun⟩ := lv
  exact ⟨aI, aQ, hB, aRk, aG, ⟨aR, aG2, aBad, aTR, CutDivD.projector_statement_of_stability D aGst, aGst⟩, aSp, aS, ⟨hM, aT4, aNN, aK, aD, aW⟩, aRun⟩

end PDV08rec

theorem chainG_rec (D : D7) (L : SizeData₂ D) (EX : ErrX D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (Z : ThetaNormsAndLinks.Loc8 X)
    (Y : BoundaryLocalData.Prov D X.P6) (K : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp)
    (Ch Ah Cq Aq C2h A2 CR Bx CT A ka CRd C1 C2 C3 CA CD : ℝ) (hCRd : 2 ≤ CRd)
    (s08b : WeightFamilies.Stmt L X.B K.CG K.AG K.CL K.AL K.CRm H.CK Ch Ah Cq Aq)
    (s08 : WeightAlgebra.Stmt L X.W K H Ch Ah Cq Aq C2h A2 CR Bx CT A)
    (s66b : BoundaryLocalData.Stmt D X.P6 Y ka)
    (sIn : ThetaNormsAndLinks.Stmt D L X Z H C2h A2 CR CT CRd)
    (s18 : LiftErrorLocal.Stmt D L EX X H C2h A2 CR CT CRd C1 C2 C3 CA CD)
    (a1 : WeightAlgebra.adm1 X.B) (a2 : WeightAlgebra.adm2 L X.W H.CA H.C1 H.A1 K.CG K.AG) (a3 : WeightAlgebra.adm3 L X.W H.CA K.Cf K.Af)
    (a4 : WeightAlgebra.ArchimedeanSignatureMatching L X.W H.CA H.C1 H.A1 K.CW K.AW) (b3 : WeightFamilies.adm3 X.B) (bB : WeightFamilies.TransferenceTheoremCond) (bC : WeightFamilies.ChowlaSelbergPeriod L)
    (a66 : BoundaryLocalData.admitted D X.P6 Y)
    (lv : ThetaNormLinkHypotheses D L X Z H C2h A2 CR CT CRd)
    (a7 : LiftErrorLocal.adm7 D X) (a8 : LiftErrorLocal.adm8 D X) (a9 : LiftErrorLocal.adm9 D X) (a12 : LiftErrorLocal.adm12 D) :
    WeightAlgebra.Conclusion1 L X.W H C2h A2 CR CT ∧ ThetaNormsAndLinks.Conclusion₂ D L X H C2h A2 CR CT CRd ∧ LiftErrorLocal.Conclusion₂ D L EX X CRd C1 C2 C3 CA CD := by
  have p08 := (quadratic_statement_of_parts L X.W K H Ch Ah Cq Aq C2h A2 CR Bx CT A s08b s08 a1 a2 a3 a4 b3 bB bC).1
  have p66 : ModuliIntegralCharts.LinkConditions D X.P6 := (s66b a66).2.2.2.2.1
  have pIn := sIn hCRd (inputs_admissible_of D L X Z H C2h A2 CR CT CRd a1 bB lv)
  exact ⟨p08, pIn, s18 (division_admissible_of_inputs D L X H C2h A2 CR CT CRd pIn p66 p08 a7 a8 a9 a12)⟩

section P18parts

variable {D : D7} {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)

def UnitClauseAtBaseTuple : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  IntegralHeckeForms.eThPMt D.nexp (nch.twI w) j b (nch.k' w) ∅ 1 ≤ LiftErrorLocal.twistV0Submodule D nch w j b ∧
    (D.what₂.Ij D.what₂.muStar j (LiftErrorLocal.plS nch w b) : ℝ) ≤ (D.what₂.places.ramIdx (LiftErrorLocal.plS nch w b) : ℝ) * X.IsgBase w j b

def TwistedIndexBound (D : D7) : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, TwistedAt D w →
  (D.what₂.jw (D.what₂.muTw w) j w : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * (D.what₂.etaJ j w : ℝ)

theorem unit_clause_admissible_of_parts (hb : UnitClauseAtBaseTuple X) (hU : ∀ w, TwistedAt D w → PDVN.UAt X w) (hjw : TwistedIndexBound D) : LiftErrorLocal.adm7 D X :=
  fun i0 w hw j hj => ⟨hb i0 w hw j hj, fun ht => ⟨hU w ht j hj, hjw i0 w hw j hj ht⟩⟩

theorem twist_admissible_of_good_twists' (h : TwGoodAt D nch X.I) : LiftErrorLocal.adm8 D X := fun _ w _ hw => h w hw

end P18parts

structure Trip (D : D7) where
  B : WeightFamilies.Prov D
  P : ModuliIntegralCharts.Prov D
  W : WeightAlgebra.Prov D B P

def tripOf {D : D7} {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) : Trip D := ⟨X.B, X.P6, X.W⟩

section Fam

variable {eps : ℝ} (Fm : FamP eps)
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.Loc (Fm.D x i) (Fm.ex x hx i).nch)

theorem theorem_zero_admissible_family_of (H : WeightAlgebra.KHyp) (C2h A2 CR : ℝ)
    (h : WeightAlgebra.ConclusionF1 Fm (fun x hx i => (XF x hx i).B) (fun x hx i => (XF x hx i).P6)
      (fun x hx i => (XF x hx i).W) H C2h A2 CR) :
    ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      LiftErrorLocal.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) (XF x hx i) H C2h A2 CR (Fm.Ct + 1) := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx h0 i => h x hx h0 i⟩

theorem jet_admissible_family_of
    (h : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.LinkConditions (Fm.D x i) (XF x hx i).P6) :
    ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.adm3 (Fm.D x i) (XF x hx i) := h

theorem division_admissible_family_of (H : WeightAlgebra.KHyp) (C2h A2 CR CRd : ℝ)
    (h8 : ThetaNormsAndLinks.ConclusionOnFamily Fm XF H C2h A2 CR CRd)
    (h66 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.LinkConditions (Fm.D x i) (XF x hx i).P6)
    (h08 : WeightAlgebra.ConclusionF1 Fm (fun x hx i => (XF x hx i).B) (fun x hx i => (XF x hx i).P6)
      (fun x hx i => (XF x hx i).W) H C2h A2 CR)
    (unit_twist_local_clauses_family : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      LiftErrorLocal.adm7 (Fm.D x i) (XF x hx i) ∧ LiftErrorLocal.adm8 (Fm.D x i) (XF x hx i) ∧ LiftErrorLocal.adm9 (Fm.D x i) (XF x hx i) ∧
        LiftErrorLocal.adm12 (Fm.D x i)) :
    LiftErrorLocal.AdmF Fm XF H C2h A2 CR CRd := by
  obtain ⟨xa, h8⟩ := h8
  obtain ⟨xb, h08⟩ := theorem_zero_admissible_family_of Fm XF H C2h A2 CR h08
  obtain ⟨xc, unit_twist_local_clauses_family⟩ := unit_twist_local_clauses_family
  refine ⟨max xa (max xb xc), fun x hx h0 i => ?_⟩
  have ha : xa ≤ x := le_trans (le_max_left _ _) h0
  have hb : xb ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h0
  have hc : xc ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h0
  obtain ⟨a7, a8, a9, a12⟩ := unit_twist_local_clauses_family x hx hc i
  exact division_admissible_of_inputs _ _ _ H C2h A2 CR _ CRd (h8 x hx ha i) (jet_admissible_family_of Fm XF h66 x hx i) (h08 x hx hb i) a7 a8 a9 a12

variable (ZF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ThetaNormsAndLinks.Loc8 (XF x hx i))

theorem inputs_admissible_family_of (H : WeightAlgebra.KHyp) (C2h A2 CR CRd : ℝ)
    (hM : WeightFamilies.familyUnitInput Fm (fun x hx i => (XF x hx i).B)) (hB : WeightFamilies.TransferenceTheoremCond)
    (lv : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      ThetaNormLinkHypotheses (Fm.D x i) (Fm.L x i) (XF x hx i) (ZF x hx i) H C2h A2 CR (Fm.Ct + 1) CRd) :
    ThetaNormsAndLinks.AdmF Fm XF ZF H C2h A2 CR CRd := by
  obtain ⟨x0, lv⟩ := lv
  refine ⟨x0, fun x hx h0 i => ?_⟩
  have h1 : WeightFamilies.adm1 (XF x hx i).B := hM x hx i
  exact inputs_admissible_of _ _ _ _ H C2h A2 CR _ CRd h1 hB (lv x hx h0 i)

end Fam

section ChainF

variable {eps : ℝ} (Fm : FamP eps)

theorem chain_sup_lattice_family (T : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Trip (Fm.D x i)) (Ob : WeightFamilies.ObjClass) (O8 : WeightAlgebra.ObjClass)
    (K : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp) (Ch Ah Cq Aq C2h A2 CR CH : ℝ)
    (s08b : WeightFamilies.PacketAlongFamilyInClass Ob K.CG K.AG K.CL K.AL K.CRm H.CK Ch Ah Cq Aq Fm CH)
    (s08 : WeightAlgebra.PeriodFamilyStatement O8 K H Ch Ah Cq Aq C2h A2 CR Fm CH)
    (ob : ∀ x hx i, Ob (Fm.L x i) (T x hx i).B)
    (o8 : ∀ x hx i, O8 (Fm.L x i) (T x hx i).B (T x hx i).P (T x hx i).W)
    (a14 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, WeightAlgebra.adm1 (T x hx i).B ∧
      WeightAlgebra.adm2 (Fm.L x i) (T x hx i).W H.CA H.C1 H.A1 K.CG K.AG ∧ WeightAlgebra.adm3 (Fm.L x i) (T x hx i).W H.CA K.Cf K.Af ∧
      WeightAlgebra.ArchimedeanSignatureMatching (Fm.L x i) (T x hx i).W H.CA H.C1 H.A1 K.CW K.AW)
    (b1 : WeightFamilies.familyUnitInput Fm (fun x hx i => (T x hx i).B)) (b3 : WeightFamilies.FamilyAdmittedLemmaThree Fm (fun x hx i => (T x hx i).B))
    (bB : WeightFamilies.TransferenceTheoremCond) (bC : WeightFamilies.ChowlaSelbergFamily Fm) :
    WeightAlgebra.ConclusionF1 Fm (fun x hx i => (T x hx i).B) (fun x hx i => (T x hx i).P) (fun x hx i => (T x hx i).W) H C2h A2 CR := by
  obtain ⟨x0, a14⟩ := a14
  obtain ⟨⟨x1, p1⟩, p2, ⟨x3, p3⟩⟩ := s08b (fun x hx i => (T x hx i).B) ob
    ⟨b1, ⟨x0, fun x hr hx i => (a14 x hr hx i).2.1.2⟩, b3, bB, bC⟩
  refine s08 (fun x hx i => (T x hx i).B) (fun x hx i => (T x hx i).P) (fun x hx i => (T x hx i).W) o8
    ⟨max x0 (max x1 x3), fun x hr hx i => ?_⟩
  have hx0 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : x1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨a1, a2, a3, a4⟩ := a14 x hr hx0 i
  exact ⟨a1, a2, a3, a4, p1 x hr hx1 i, p2 x hr i, p3 x hr hx3 i⟩

variable (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.Loc (Fm.D x i) (Fm.ex x hx i).nch)
  (ZF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ThetaNormsAndLinks.Loc8 (XF x hx i))
  (YF : BoundaryLocalData.ProvF Fm (fun x hx i => (XF x hx i).P6))

structure LvG (Ob : WeightFamilies.ObjClass) (O8 : WeightAlgebra.ObjClass) (O18 : LiftErrorLocal.ObjClass) (K : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp)
    (C2h A2 CR CRd : ℝ) : Prop where
  ob : ∀ x hx i, Ob (Fm.L x i) (XF x hx i).B
  o8 : ∀ x hx i, O8 (Fm.L x i) (XF x hx i).B (XF x hx i).P6 (XF x hx i).W
  o18 : ∀ x hx i, O18 (Fm.L x i) (Fm.ex x hx i).nch (XF x hx i)
  a14 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      WeightAlgebra.adm2 (Fm.L x i) (XF x hx i).W H.CA H.C1 H.A1 K.CG K.AG ∧
      WeightAlgebra.adm3 (Fm.L x i) (XF x hx i).W H.CA K.Cf K.Af ∧
      WeightAlgebra.ArchimedeanSignatureMatching (Fm.L x i) (XF x hx i).W H.CA H.C1 H.A1 K.CW K.AW
  b1 : WeightFamilies.familyUnitInput Fm (fun x hx i => (XF x hx i).B)
  b3 : WeightFamilies.FamilyAdmittedLemmaThree Fm (fun x hx i => (XF x hx i).B)
  bB : WeightFamilies.TransferenceTheoremCond
  bC : WeightFamilies.ChowlaSelbergFamily Fm
  a66 : BoundaryLocalData.AdmFx Fm (fun x hx i => (XF x hx i).P6) YF
  lv : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      ThetaNormLinkHypotheses (Fm.D x i) (Fm.L x i) (XF x hx i) (ZF x hx i) H C2h A2 CR (Fm.Ct + 1) CRd
  a79 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      UnitClauseAtBaseTuple (XF x hx i) ∧ TwistedIndexBound (Fm.D x i) ∧ LiftErrorLocal.adm9 (Fm.D x i) (XF x hx i)
  aU : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, ∀ w, TwistedAt (Fm.D x i) w → PDVN.UAt (XF x hx i) w
  aTG : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, TwGoodAt (Fm.D x i) (Fm.ex x hx i).nch (XF x hx i).I
  a12 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, N.LocsCoverTw (Fm.D x i)

theorem LvG.unit_twist_local_clauses_family {Ob : WeightFamilies.ObjClass} {O8 : WeightAlgebra.ObjClass} {O18 : LiftErrorLocal.ObjClass} {K : WeightAlgebra.KAdm} {H : WeightAlgebra.KHyp} {C2h A2 CR CRd : ℝ}
    (lv : LvG Fm XF ZF YF Ob O8 O18 K H C2h A2 CR CRd) :
    ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      LiftErrorLocal.adm7 (Fm.D x i) (XF x hx i) ∧ LiftErrorLocal.adm8 (Fm.D x i) (XF x hx i) ∧ LiftErrorLocal.adm9 (Fm.D x i) (XF x hx i) ∧
        LiftErrorLocal.adm12 (Fm.D x i) := by
  obtain ⟨a, h1⟩ := lv.a79
  obtain ⟨b, h2⟩ := lv.aU
  obtain ⟨c, h3⟩ := lv.aTG
  obtain ⟨d, h4⟩ := lv.a12
  refine ⟨max (max a b) (max c d), fun x hx h0 i => ?_⟩
  have ha : a ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h0
  have hb : b ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h0
  have hc : c ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h0
  have hd : d ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h0
  obtain ⟨b7, j7, h9⟩ := h1 x hx ha i
  exact ⟨unit_clause_admissible_of_parts _ b7 (h2 x hx hb i) j7, twist_admissible_of_good_twists' _ (h3 x hx hc i), h9, h4 x hx hd i⟩

theorem chainGF (Ob : WeightFamilies.ObjClass) (O8 : WeightAlgebra.ObjClass) (O18 : LiftErrorLocal.ObjClass) (K : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp)
    (Ch Ah Cq Aq C2h A2 CR ka CRd C1 C2 C3 CA CD CH : ℝ)
    (s08b : WeightFamilies.PacketAlongFamilyInClass Ob K.CG K.AG K.CL K.AL K.CRm H.CK Ch Ah Cq Aq Fm CH)
    (s08 : WeightAlgebra.PeriodFamilyStatement O8 K H Ch Ah Cq Aq C2h A2 CR Fm CH)
    (s66b : BoundaryLocalData.FamilyKeyFormulaOfAdmissible Fm (fun x hx i => (XF x hx i).P6) YF ka)
    (sIn : ThetaNormsAndLinks.AdmF Fm XF ZF H C2h A2 CR CRd → ThetaNormsAndLinks.ConclusionOnFamily Fm XF H C2h A2 CR CRd)
    (s18 : LiftErrorLocal.KudlaFamilyStatement O18 H C2h A2 CR CRd C1 C2 C3 CA CD Fm CH)
    (lv : LvG Fm XF ZF YF Ob O8 O18 K H C2h A2 CR CRd) :
    WeightAlgebra.ConclusionF1 Fm (fun x hx i => (XF x hx i).B) (fun x hx i => (XF x hx i).P6)
                  (fun x hx i => (XF x hx i).W) H C2h A2 CR ∧
      ThetaNormsAndLinks.ConclusionOnFamily Fm XF H C2h A2 CR CRd ∧ LiftErrorLocal.OrbitValuationBound Fm XF CRd C1 C2 C3 CA CD := by
  have p08 := chain_sup_lattice_family Fm (fun x hx i => tripOf (XF x hx i)) Ob O8 K H Ch Ah Cq Aq C2h A2 CR CH s08b s08 lv.ob lv.o8 (lv.a14.imp fun _ h x hx h0 i => ⟨lv.b1 x hx i, h x hx h0 i⟩) lv.b1
    lv.b3 lv.bB lv.bC
  have p66 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.LinkConditions (Fm.D x i) (XF x hx i).P6 :=
    fun x hx i => (s66b lv.a66 x hx i).2.2.2.2
  have pIn := sIn (inputs_admissible_family_of Fm XF ZF H C2h A2 CR CRd lv.b1 lv.bB lv.lv)
  exact ⟨p08, pIn, s18 XF lv.o18 (division_admissible_family_of Fm XF H C2h A2 CR CRd pIn p66 p08 lv.unit_twist_local_clauses_family)⟩

theorem degree_bound_family_of_inputs (C1 C2 C3 CD : ℝ)
    (sC : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.PropositionCStatement (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX (XF x hx i)
      C1 C2 C3)
    (sD : ∀ x (i : Fm.Ix x), LiftErrorLocal.KappaDegreeStatement (Fm.D x i) (Fm.L x i) CD)
    (lv : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      ThetaNormsAndLinks.admissible_unitary_of_inputs (Fm.D x i) (XF x hx i) (ZF x hx i) ∧ ThetaNormsAndLinks.SandwichExists (Fm.D x i) (XF x hx i) ∧
        LiftErrorLocal.adm9 (Fm.D x i) (XF x hx i)) :
    ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      LiftErrorLocal.PropositionCLatticeBound (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1 C2 ∧
        LiftErrorLocal.JetConsequence (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1 C2 C3 ∧ LiftErrorLocal.ThetaAdjointPositiveScalar (Fm.D x i) (Fm.L x i) CD := by
  obtain ⟨x0, lv⟩ := lv
  refine ⟨x0, fun x hx h0 i => ?_⟩
  obtain ⟨aI, aQ, a9⟩ := lv x hx h0 i
  have h := sC x hx i (proposition_C_hypotheses_of _ _ (ThetaNormsAndLinks.stmt1 _ _ _ aI) (ThetaNormsAndLinks.stmt2 _ _ aQ) a9)
  exact ⟨h.1, h.2, sD x i⟩

theorem degree_bound_family_of_inputs' (C1 C2 C3 : ℝ)
    (sC : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.PropositionCStatement (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX (XF x hx i) C1 C2 C3)
    (lv : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      ThetaNormsAndLinks.admissible_unitary_of_inputs (Fm.D x i) (XF x hx i) (ZF x hx i) ∧ ThetaNormsAndLinks.SandwichExists (Fm.D x i) (XF x hx i) ∧
        LiftErrorLocal.adm9 (Fm.D x i) (XF x hx i)) :
    ∃ CD x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      LiftErrorLocal.PropositionCLatticeBound (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1 C2 ∧
        LiftErrorLocal.JetConsequence (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1 C2 C3 ∧ LiftErrorLocal.ThetaAdjointPositiveScalar (Fm.D x i) (Fm.L x i) CD := by
  obtain ⟨CD, hD⟩ := CutKapD.kappa_degree_bound_holds
  exact ⟨CD, degree_bound_family_of_inputs Fm XF ZF C1 C2 C3 CD sC (fun x i => hD (Fm.D x i) (Fm.L x i)) lv⟩

end ChainF

abbrev gK (sb : WeightFamilies.Sel) (K0 : WeightAlgebra.KAdm) : WeightAlgebra.KAdm := { K0 with CL := sb.C K0.CG K0.AG, AL := sb.A K0.CG K0.AG }

abbrev gCq (sb : WeightFamilies.Sel) (s8 : WeightAlgebra.Sel) (K0 : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp) : ℝ :=
  sb.Cc K0.CG K0.AG K0.CRm H.CK (s8.Ch (gK sb K0) H) (s8.Ah (gK sb K0).deg H.deg)

abbrev gAq (sb : WeightFamilies.Sel) (s8 : WeightAlgebra.Sel) (K0 : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp) : ℝ :=
  sb.Ac K0.CG K0.AG K0.CRm H.CK (s8.Ch (gK sb K0) H) (s8.Ah (gK sb K0).deg H.deg)

abbrev rankConstantOfSelection (sb : WeightFamilies.Sel) (s8 : WeightAlgebra.Sel) (K0 : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp) : ℝ :=
  s8.C2 (gK sb K0) H (gCq sb s8 K0 H) (gAq sb s8 K0 H)

abbrev rankExponentOfSelection (sb : WeightFamilies.Sel) (s8 : WeightAlgebra.Sel) (K0 : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp) : ℝ :=
  s8.A2 (gK sb K0).deg H.deg (gAq sb s8 K0 H)

abbrev gCR (sb : WeightFamilies.Sel) (s8 : WeightAlgebra.Sel) (K0 : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp) : ℝ :=
  s8.CR (gK sb K0).deg H.deg (gAq sb s8 K0 H)

theorem chainG (𝒞 : FamClass) (Ob : WeightFamilies.ObjClass) (O8 : WeightAlgebra.ObjClass) (O18 : LiftErrorLocal.ObjClass) (ka : ℝ)
    (h08b : WeightFamilies.ClosedAbsoluteShare Ob 𝒞) (h08 : WeightAlgebra.ClosedSupNormFirstForm O8 𝒞) (h66 : BoundaryLocalData.ClosedFamilyKeyFormula 𝒞 ka)
    (hIn : ThetaNormsAndLinks.ClosedAbsoluteShare 𝒞)
    (h18 : LiftErrorLocal.ClosedAbsoluteShare O18 𝒞) :
    ∃ (sb : WeightFamilies.Sel) (s8 : WeightAlgebra.Sel) (C1 C2 C3 CA CD : ℝ), Closed 𝒞 fun Fm _ =>
      ∀ (K0 : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp) (CRd : ℝ), 2 ≤ K0.CRm → 2 ≤ CRd →
      ∀ (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.Loc (Fm.D x i) (Fm.ex x hx i).nch)
        (ZF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ThetaNormsAndLinks.Loc8 (XF x hx i))
        (YF : BoundaryLocalData.ProvF Fm (fun x hx i => (XF x hx i).P6)),
        LvG Fm XF ZF YF Ob O8 O18 (gK sb K0) H (rankConstantOfSelection sb s8 K0 H) (rankExponentOfSelection sb s8 K0 H) (gCR sb s8 K0 H) CRd →
        WeightAlgebra.ConclusionF1 Fm (fun x hx i => (XF x hx i).B) (fun x hx i => (XF x hx i).P6)
                      (fun x hx i => (XF x hx i).W) H (rankConstantOfSelection sb s8 K0 H) (rankExponentOfSelection sb s8 K0 H) (gCR sb s8 K0 H) ∧
          ThetaNormsAndLinks.ConclusionOnFamily Fm XF H (rankConstantOfSelection sb s8 K0 H) (rankExponentOfSelection sb s8 K0 H) (gCR sb s8 K0 H) CRd ∧
          LiftErrorLocal.OrbitValuationBound Fm XF CRd C1 C2 C3 CA CD := by
  obtain ⟨sb, h08b⟩ := h08b
  obtain ⟨s8, h08⟩ := h08
  obtain ⟨C1, C2, C3, CA, CD, h18⟩ := h18
  refine ⟨sb, s8, C1, C2, C3, CA, CD, (h08b.and (h08.and (h66.and (hIn.and h18)))).imp
    fun Fm CH _ h K0 H CRd hCRm hCRd XF ZF YF lv => ?_⟩
  obtain ⟨a, b, e, c, d⟩ := h
  exact chainGF Fm XF ZF YF Ob O8 O18 (gK sb K0) H (s8.Ch (gK sb K0) H) (s8.Ah (gK sb K0).deg H.deg) (gCq sb s8 K0 H)
    (gAq sb s8 K0 H) (rankConstantOfSelection sb s8 K0 H) (rankExponentOfSelection sb s8 K0 H) (gCR sb s8 K0 H) ka CRd C1 C2 C3 CA CD CH
    (a K0.CG K0.AG K0.CRm H.CK (s8.Ch (gK sb K0) H) (s8.Ah (gK sb K0).deg H.deg))
    (b (gK sb K0) H (gCq sb s8 K0 H) (gAq sb s8 K0 H) hCRm) (e _ YF) (c H _ _ _ CRd hCRd XF ZF) (d H _ _ _ CRd hCRd) lv

section ON

variable {D : D7} {CH : NChoice D} {Xd : DivX D}

theorem PDVN_AdmRun_of (X : LiftErrorLocal.Loc D CH) (L : SizeData₂ D) (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ)
    (h08 : WeightAlgebra.Conclusion1 L X.W H C2 A2 CR CT) (hLB : LiftErrorLocal.LemmaBWeightBound D X CRd) (hWB : ThetaNormsAndLinks.WeightGeneratorsInLattice D X)
    (h11 : ThetaNormsAndLinks.RunConditions D L X H C2 A2 CR CT CRd) : PDVN.AdmRun X L H C2 A2 CR CT CRd := fun _ => ⟨h08, hLB, hWB, h11⟩

theorem proposition_A_type_primes_admissible (L : SizeData₂ D) (O : PDVN.ONObj D CH Xd) (CA : ℝ) (h : LiftErrorLocal.ConjugationNormInvariance D L O.X CA) : PDVN.admA L O CA := h

theorem off_type_lattices_admissible_of (O : PDVN.ONObj D CH Xd) (h : ThetaNormsAndLinks.AtEveryPlace D O.X) (h' : ThetaNormsAndLinks.LinkLatticesEveryPlace D O.X') : PDVN.OffTypePrimeConditions O :=
  ThetaNormsAndLinks.offTypePrime_of D O h.1 h.2.1 h.2.2.1 h.2.2.2 h'

theorem orbit_content_admissible_of (O : PDVN.ONObj D CH Xd) (C6 : ℝ) (h : CartierLocalBounds.Conclusion5 D Xd O.X.P6 O.c6 C6)
    (h' : CartierLocalBounds.Conclusion5 D Xd O.X'.P6 O.c6' C6) : PDVN.OrbitContentCond O C6 := ⟨h, h'⟩

def ONIn (L : SizeData₂ D) (O : PDVN.ONObj D CH Xd) (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd C6 CA : ℝ) : Prop :=
  (WeightAlgebra.Conclusion1 L O.X.W H C2 A2 CR CT ∧ LiftErrorLocal.LemmaBWeightBound D O.X CRd ∧ ThetaNormsAndLinks.RunConditions D L O.X H C2 A2 CR CT CRd) ∧
  (WeightAlgebra.Conclusion1 L O.X'.W H C2 A2 CR CT ∧ LiftErrorLocal.LemmaBWeightBound D O.X' CRd ∧ ThetaNormsAndLinks.WeightGeneratorsInLattice D O.X' ∧ ThetaNormsAndLinks.RunConditions D L O.X' H C2 A2 CR CT CRd) ∧
  (LiftErrorLocal.ConjugationNormInvariance D L O.X CA ∧ ThetaNormsAndLinks.LinkConditions D O.X) ∧
  (ThetaNormsAndLinks.AtEveryPlace D O.X ∧ ThetaNormsAndLinks.LinkLatticesEveryPlace D O.X') ∧
  (CartierLocalBounds.Conclusion5 D Xd O.X.P6 O.c6 C6 ∧ CartierLocalBounds.Conclusion5 D Xd O.X'.P6 O.c6' C6)

def ONLv (L : SizeData₂ D) (O : PDVN.ONObj D CH Xd) (C6 Cd Cs : ℝ) : Prop :=
  L.FDef ∧ PDVN.unitBoundAtTwistedPlaces O ∧ PDVN.DepthFromContent L O C6 Cd ∧ PDVN.TypePrimeSizeConds L O Cs ∧ PDVN.TwistedPlacesCover D

theorem PDVN_AdmON_of (L : SizeData₂ D) (O : PDVN.ONObj D CH Xd) (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd C6 Cd Cs CA : ℝ)
    (h : ONIn L O H C2 A2 CR CT CRd C6 CA) (lv : ONLv L O C6 Cd Cs) :
    PDVN.AdmON L O H C2 A2 CR CT CRd C6 Cd Cs CA := by
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, bW, b3⟩, ⟨pA, g10⟩, ⟨gA, gL'⟩, ⟨c1, c2⟩⟩ := h
  obtain ⟨l2, l4, l6, l7, l8⟩ := lv
  exact ⟨l2, PDVN_AdmRun_of O.X L H C2 A2 CR CT CRd a1 a2 g10.2 a3, PDVN_AdmRun_of O.X' L H C2 A2 CR CT CRd b1 b2 bW b3,
    proposition_A_type_primes_admissible L O CA pA, l4, off_type_lattices_admissible_of O gA gL', orbit_content_admissible_of O C6 c1 c2, l6, l7, l8, fun _ w _ _ => gA.2.1 w⟩

theorem ONIn_of (L : SizeData₂ D) (O : PDVN.ONObj D CH Xd) (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd C6 CA : ℝ)
    (p08 : WeightAlgebra.Conclusion1 L O.X.W H C2 A2 CR CT) (p08' : WeightAlgebra.Conclusion1 L O.X'.W H C2 A2 CR CT) (pA : LiftErrorLocal.ConjugationNormInvariance D L O.X CA)
    (pIn : ThetaNormsAndLinks.Conclusion₂ D L O.X H C2 A2 CR CT CRd)
    (r1 : ThetaNormsAndLinks.Conclusion1 D O.X') (r2 : ThetaNormsAndLinks.Conclusion2 D O.X') (r3b : ThetaNormsAndLinks.CoveringRadiusFunction D O.X' CRd) (rWB : ThetaNormsAndLinks.WeightGeneratorsInLattice D O.X')
    (r11 : ThetaNormsAndLinks.RunConditions D L O.X' H C2 A2 CR CT CRd) (rLK : ThetaNormsAndLinks.LinkLatticesEveryPlace D O.X')
    (p66 : ModuliIntegralCharts.LinkConditions D O.X.P6) (p66' : ModuliIntegralCharts.LinkConditions D O.X'.P6)
    (sLB : LiftErrorLocal.LemmaBStatementAlt D O.X CRd) (sLB' : LiftErrorLocal.LemmaBStatementAlt D O.X' CRd)
    (s02 : CartierLocalBounds.Stmt D Xd O.X.P6 O.c6 C6) (s02' : CartierLocalBounds.Stmt D Xd O.X'.P6 O.c6' C6)
    (a02 : CartierLocalBounds.admitted D Xd O.X.P6 O.c6) (a02' : CartierLocalBounds.admitted D Xd O.X'.P6 O.c6') :
    ONIn L O H C2 A2 CR CT CRd C6 CA := by
  obtain ⟨q1, q2, q3b, -, -, -, -, q10, q11, qA⟩ := pIn
  exact ⟨⟨p08, sLB (lemma_B_hypotheses_of D O.X CRd q1 q2 p66 q3b), q11⟩,
    ⟨p08', sLB' (lemma_B_hypotheses_of D O.X' CRd r1 r2 p66' r3b), rWB, r11⟩, ⟨pA, q10⟩, ⟨qA, rLK⟩,
    ⟨(s02 a02).2.2.2.2, (s02' a02').2.2.2.2⟩⟩

end ON

section ONF

variable {eps : ℝ} (Fm : FamP eps) (OF : PDVN.ONObjF Fm)

theorem PDVN_AdmONF_of (H : WeightAlgebra.KHyp) (C2 A2 CR CRd C6 Cd Cs CA : ℝ)
    (h : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      ONIn (Fm.L x i) (OF x hx i) H C2 A2 CR (Fm.Ct + 1) CRd C6 CA ∧ ONLv (Fm.L x i) (OF x hx i) C6 Cd Cs) :
    PDVN.AdmONF Fm OF H C2 A2 CR CRd C6 Cd Cs CA := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx h0 i => PDVN_AdmON_of _ _ H C2 A2 CR _ CRd C6 Cd Cs CA (h x hx h0 i).1 (h x hx h0 i).2⟩

theorem ONTwJF_of (H : WeightAlgebra.KHyp) (C2 A2 CR CRd C6 Cd Cs CA C CHc : ℝ)
    (sON : PDVN.FamilyOntoIndicesOfAdmissible H C2 A2 CR CRd C6 Cd Cs CA C Fm OF CHc)
    (h : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      ONIn (Fm.L x i) (OF x hx i) H C2 A2 CR (Fm.Ct + 1) CRd C6 CA ∧ ONLv (Fm.L x i) (OF x hx i) C6 Cd Cs)
    (hg : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      PDVN.DomON (Fm.D x i) (Fm.L x i) (Fm.parT x hx i).nWn (Fm.parT x hx i).CP ∧ TwConjAt (Fm.D x i) (Fm.ex x hx i).nch ∧ PDVN.TraceLatticeInclusion (Fm.D x i) (OF x hx i).X.I.E (OF x hx i).T ∧
        TwGoodAt (Fm.D x i) (Fm.ex x hx i).nch (OF x hx i).X.I) :
    ∃ x0 : ℝ, ∀ x (_ : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      PDVN.ONTw (Fm.D x i) (Fm.L x i) C ∧ PDVN.ONTwJ (Fm.D x i) (Fm.L x i) C :=
  (sON (PDVN_AdmONF_of Fm OF H C2 A2 CR CRd C6 Cd Cs CA h)).concl hg

end ONF

section ONchain

variable {eps : ℝ} (Fm : FamP eps)

theorem thr_and {P Q : ∀ x, Fm.x1 < x → Fm.Ix x → Prop}
    (hP : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, P x hx i)
    (hQ : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, Q x hx i) :
    ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, P x hx i ∧ Q x hx i := by
  obtain ⟨a, hP⟩ := hP
  obtain ⟨b, hQ⟩ := hQ
  exact ⟨max a b, fun x hx h0 i => ⟨hP x hx (le_trans (le_max_left _ _) h0) i, hQ x hx (le_trans (le_max_right _ _) h0) i⟩⟩

variable (OF : PDVN.ONObjF Fm)

theorem ONInF_of (H : WeightAlgebra.KHyp) (C2h A2 CR CRd C6 C1 C2 C3 CA CD : ℝ)
    (p08 : WeightAlgebra.ConclusionF1 Fm (fun x hx i => (OF x hx i).X.B)
      (fun x hx i => (OF x hx i).X.P6)
      (fun x hx i => (OF x hx i).X.W) H C2h A2 CR)
    (p08' : WeightAlgebra.ConclusionF1 Fm (fun x hx i => (OF x hx i).X'.B)
      (fun x hx i => (OF x hx i).X'.P6)
      (fun x hx i => (OF x hx i).X'.W) H C2h A2 CR)
    (pIn : ThetaNormsAndLinks.ConclusionOnFamily Fm (fun x hx i => (OF x hx i).X) H C2h A2 CR CRd)
    (pIn' : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      LiftErrorLocal.LemmaBWeightBound (Fm.D x i) (OF x hx i).X' CRd ∧ ThetaNormsAndLinks.WeightGeneratorsInLattice (Fm.D x i) (OF x hx i).X' ∧
        ThetaNormsAndLinks.RunConditions (Fm.D x i) (Fm.L x i) (OF x hx i).X' H C2h A2 CR (Fm.Ct + 1) CRd ∧ ThetaNormsAndLinks.LinkLatticesEveryPlace (Fm.D x i) (OF x hx i).X')
    (p18 : LiftErrorLocal.OrbitValuationBound Fm (fun x hx i => (OF x hx i).X) CRd C1 C2 C3 CA CD)
    (p02 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      CartierLocalBounds.Conclusion5 (Fm.D x i) (Fm.X x i) (OF x hx i).X.P6 (OF x hx i).c6 C6 ∧
        CartierLocalBounds.Conclusion5 (Fm.D x i) (Fm.X x i) (OF x hx i).X'.P6 (OF x hx i).c6' C6) :
    ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      ONIn (Fm.L x i) (OF x hx i) H C2h A2 CR (Fm.Ct + 1) CRd C6 CA := by
  have q08 := theorem_zero_admissible_family_of Fm (fun x hx i => (OF x hx i).X) H C2h A2 CR p08
  have q08' := theorem_zero_admissible_family_of Fm (fun x hx i => (OF x hx i).X') H C2h A2 CR p08'
  obtain ⟨x0, h⟩ := thr_and Fm q08 (thr_and Fm q08' (thr_and Fm pIn (thr_and Fm pIn' (thr_and Fm p18 p02))))
  refine ⟨x0, fun x hx h0 i => ?_⟩
  obtain ⟨a, a', ⟨-, -, -, -, -, -, -, q10, q11, qA⟩, ⟨rLB, rWB, r11, rLK⟩, b, c⟩ := h x hx h0 i
  exact ⟨⟨a, b.2.2.2.1, q11⟩, ⟨a', rLB, rWB, r11⟩, ⟨b.2.2.2.2.2.2.1, q10⟩, ⟨qA, rLK⟩, c⟩

end ONchain

section ONstmts

variable {eps : ℝ} (Fm : FamP eps) (OF : PDVN.ONObjF Fm)

theorem ONInF_of_stmts
    (ZF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ThetaNormsAndLinks.Loc8 (OF x hx i).X)
    (ZF' : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ThetaNormsAndLinks.Loc8 (OF x hx i).X')
    (YF : BoundaryLocalData.ProvF Fm (fun x hx i => (OF x hx i).X.P6)) (YF' : BoundaryLocalData.ProvF Fm (fun x hx i => (OF x hx i).X'.P6))
    (Ob : WeightFamilies.ObjClass) (O8 : WeightAlgebra.ObjClass) (O18 : LiftErrorLocal.ObjClass) (K : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp)
    (Ch Ah Cq Aq C2h A2 CR ka ka' CRd C1 C2 C3 CA CD CH C6 : ℝ)
    (s08b : WeightFamilies.PacketAlongFamilyInClass Ob K.CG K.AG K.CL K.AL K.CRm H.CK Ch Ah Cq Aq Fm CH)
    (s08 : WeightAlgebra.PeriodFamilyStatement O8 K H Ch Ah Cq Aq C2h A2 CR Fm CH)
    (s66b : BoundaryLocalData.FamilyKeyFormulaOfAdmissible Fm (fun x hx i => (OF x hx i).X.P6) YF ka)
    (s66b' : BoundaryLocalData.FamilyKeyFormulaOfAdmissible Fm (fun x hx i => (OF x hx i).X'.P6) YF' ka')
    (sIn : ThetaNormsAndLinks.AdmF Fm (fun x hx i => (OF x hx i).X) ZF H C2h A2 CR CRd → ThetaNormsAndLinks.ConclusionOnFamily Fm (fun x hx i => (OF x hx i).X) H C2h A2 CR CRd)
    (sIn' : ThetaNormsAndLinks.AdmF Fm (fun x hx i => (OF x hx i).X') ZF' H C2h A2 CR CRd → ThetaNormsAndLinks.ConclusionOnFamily Fm (fun x hx i => (OF x hx i).X') H C2h A2 CR CRd)
    (s18 : LiftErrorLocal.KudlaFamilyStatement O18 H C2h A2 CR CRd C1 C2 C3 CA CD Fm CH)
    (lv : LvG Fm (fun x hx i => (OF x hx i).X) ZF YF Ob O8 O18 K H C2h A2 CR CRd)
    (lv' : LvG Fm (fun x hx i => (OF x hx i).X') ZF' YF' Ob O8 O18 K H C2h A2 CR CRd)
    (s02 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      CartierLocalBounds.Stmt (Fm.D x i) (Fm.X x i) (OF x hx i).X.P6 (OF x hx i).c6 C6 ∧ CartierLocalBounds.Stmt (Fm.D x i) (Fm.X x i) (OF x hx i).X'.P6 (OF x hx i).c6' C6)
    (a02 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      CartierLocalBounds.admitted (Fm.D x i) (Fm.X x i) (OF x hx i).X.P6 (OF x hx i).c6 ∧ CartierLocalBounds.admitted (Fm.D x i) (Fm.X x i) (OF x hx i).X'.P6 (OF x hx i).c6') :
    ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      ONIn (Fm.L x i) (OF x hx i) H C2h A2 CR (Fm.Ct + 1) CRd C6 CA := by
  obtain ⟨p08, pIn, p18⟩ := chainGF Fm (fun x hx i => (OF x hx i).X) ZF YF Ob O8 O18 K H Ch Ah Cq Aq C2h A2 CR ka CRd C1 C2 C3 CA CD CH
    s08b s08 s66b sIn s18 lv
  obtain ⟨p08', pIn', p18'⟩ := chainGF Fm (fun x hx i => (OF x hx i).X') ZF' YF' Ob O8 O18 K H Ch Ah Cq Aq C2h A2 CR ka' CRd C1 C2 C3 CA
    CD CH s08b s08 s66b' sIn' s18 lv'
  have q' : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      LiftErrorLocal.LemmaBWeightBound (Fm.D x i) (OF x hx i).X' CRd ∧ ThetaNormsAndLinks.WeightGeneratorsInLattice (Fm.D x i) (OF x hx i).X' ∧
        ThetaNormsAndLinks.RunConditions (Fm.D x i) (Fm.L x i) (OF x hx i).X' H C2h A2 CR (Fm.Ct + 1) CRd ∧ ThetaNormsAndLinks.LinkLatticesEveryPlace (Fm.D x i) (OF x hx i).X' := by
    obtain ⟨x0, h⟩ := thr_and Fm p18' (thr_and Fm pIn' lv'.lv)
    refine ⟨x0, fun x hx h0 i => ?_⟩
    obtain ⟨a, b, c⟩ := h x hx h0 i
    obtain ⟨-, -, -, aLB, -⟩ := a
    obtain ⟨-, -, -, -, -, -, -, -, b11, -, -, -, bLK⟩ := b
    obtain ⟨-, -, -, -, -, -, -, ⟨-, -, -, -, cWB⟩, -⟩ := c
    exact ⟨aLB, cWB, b11, bLK⟩
  have q02 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      CartierLocalBounds.Conclusion5 (Fm.D x i) (Fm.X x i) (OF x hx i).X.P6 (OF x hx i).c6 C6 ∧
        CartierLocalBounds.Conclusion5 (Fm.D x i) (Fm.X x i) (OF x hx i).X'.P6 (OF x hx i).c6' C6 := by
    obtain ⟨x0, h⟩ := thr_and Fm s02 a02
    exact ⟨x0, fun x hx h0 i => ⟨((h x hx h0 i).1.1 (h x hx h0 i).2.1).2.2.2.2, ((h x hx h0 i).1.2 (h x hx h0 i).2.2).2.2.2.2⟩⟩
  exact ONInF_of Fm OF H C2h A2 CR CRd C6 C1 C2 C3 CA CD p08 p08' pIn q' p18 q02

end ONstmts

end Formalism.MainNotions.DIV

end
