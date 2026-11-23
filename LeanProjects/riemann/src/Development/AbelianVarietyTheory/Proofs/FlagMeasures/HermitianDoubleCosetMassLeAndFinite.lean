import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolumeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTermsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMassEqSumFrameClassesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameClassesTotalWeightLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluingImageCardPowLeDefectGroupCardStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTermCountFrameClassLeStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MassGlue

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}

omit [IsNonarchimedeanLocalField F] [CharZero F] in

theorem sumCls_le (S : Frames L r k) (φ : Set S.FrP → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ C, φ C ≤ c) :
    S.sumCls φ ≤ (S.sumCls fun _ => 1) * c := by
  unfold Frames.sumCls
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs
  · rw [mul_one]
    gcongr
    exact h _
  · simp

theorem mass_le (S : Frames L r k) (d : S.Datum) (j : ℕ) :
    (S.mass d fun Λ => S.cardI d Λ = j) ≤
      ENNReal.ofReal (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (j : ℝ) ^ (k - 1)) := by
  by_cases hex : ∃ Λ, S.IsTerm d Λ
  · obtain ⟨Λ₀, h₀⟩ := hex
    have hH : 1 ≤ S.Hp := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ₀ h₀).2.2.2.2.1
    rw [GlobalTheory.T.hermitianMass_eq_sum_frameClasses L r k S d _ (fun h hh Λ hT hP => by
      rw [(GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d Λ hT h hh).2.2.2.2.2.2.1]; exact hP)]
    refine (sumCls_le S _ _ fun C => GlobalTheory.T.hermitianTermCount_frameClass_le L r k S d C j).trans ?_
    refine (mul_le_mul_left (GlobalTheory.T.hermitianFrameClasses_total_weight_le L r k S ⟨d, Λ₀, h₀⟩) _).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_assoc, ← pow_add]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hH ?_) (by positivity)
    omega
  · have : (S.mass d fun Λ => S.cardI d Λ = j) = 0 := by
      unfold Frames.mass
      refine ENNReal.tsum_eq_zero.2 fun o => if_neg fun h => hex ⟨_, h.1⟩
    rw [this]
    exact zero_le

theorem finite_fibre (S : Frames L r k) (d : S.Datum) (C : Set S.FrP) :
    {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C}.Finite := by
  have h1 : ∀ j : ℕ, {Λ | S.IsTerm d Λ ∧ S.cardI d Λ = j ∧ S.Fr d Λ = C}.Finite := fun j => by
    have h := (GlobalTheory.T.hermitianTermCount_frameClass_le L r k S d C j).trans_lt ENNReal.ofReal_lt_top
    unfold Frames.nT at h
    rw [← Set.encard_lt_top_iff]
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc] at h
    simp at h
  refine ((Set.finite_Iic S.a.toNat).biUnion fun i _ =>
    (Set.finite_Iic (S.q ^ i)).biUnion fun j _ => h1 j).subset ?_
  rintro Λ ⟨hT, hC⟩
  obtain ⟨i, hi, hb⟩ := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.1
  have h2 := (GlobalTheory.T.gluingImage_card_pow_le_defectGroup_card L r k S d Λ hT).2.1
  simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_setOf_eq]
  exact ⟨i, by omega, S.cardI d Λ, hb ▸ h2, hT, rfl, hC⟩

theorem finite_cls (S : Frames L r k) (h : ∃ d Λ, S.IsTerm d Λ) :
    {o : MulAction.orbitRel.Quotient S.St (Set S.FrP) | S.IsIntCls o.out}.Finite := by
  have h1 := ((GlobalTheory.T.hermitianFrameClasses_total_weight_le L r k S h).trans_lt ENNReal.ofReal_lt_top).ne
  unfold Frames.sumCls at h1
  refine (ENNReal.finite_const_le_of_tsum_ne_top h1 (ε := 1) one_ne_zero).subset fun o ho => ?_
  have ho' : S.IsIntCls o.out := ho
  simp only [Set.mem_setOf_eq, if_pos ho', mul_one]
  exact ENNReal.one_le_ofReal.2 ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).2 _ ho'.1).2.2.1

theorem finite_orbits (S : Frames L r k) (d : S.Datum) :
    {o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) | S.IsTerm d o.out}.Finite := by
  by_cases hex : ∃ Λ, S.IsTerm d Λ
  · obtain ⟨Λ₀, h₀⟩ := hex
    refine (((finite_cls S ⟨d, Λ₀, h₀⟩).biUnion fun o _ => finite_fibre S d o.out).image
      (fun Λ => (Quotient.mk _ Λ : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V)))).subset ?_
    intro o ho
    have hT : S.IsTerm d o.out := ho
    let o' : MulAction.orbitRel.Quotient S.St (Set S.FrP) := Quotient.mk _ (S.Fr d o.out)
    obtain ⟨h, hh⟩ : o'.out ∈ MulAction.orbit S.St (S.Fr d o.out) :=
      MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel S.St (Set S.FrP)) _)
    have hA := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d _ hT h.1 h.2
    have hF : S.Fr d (h.1 • o.out) = o'.out := hA.2.2.2.2.1.trans hh
    refine ⟨h.1 • o.out, ?_, ?_⟩
    · simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨o', hF ▸ (GlobalTheory.HL.TermBasic.term_basic L r k S d _ hA.1).2.2.2.2.2.2.1, hA.1, hF⟩
    · refine Eq.trans ?_ (Quotient.out_eq o)
      exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨h, rfl⟩)
  · refine Set.finite_empty.subset fun o ho => hex ⟨_, ho⟩

end GlobalTheory.HL.MassGlue

theorem GlobalTheory.HL.MassGlue.mass_le_and_finite : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 1 ≤ k → ∀ d : S.Datum, (∀ j : ℕ, (S.mass d fun Λ => S.cardI d Λ = j) ≤ ENNReal.ofReal (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (j : ℝ) ^ (k - 1))) ∧ {o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) | S.IsTerm d o.out}.Finite := by
  intro F _ _ _ _ _ E _ _ _ L r k S _ d
  exact ⟨GlobalTheory.HL.MassGlue.mass_le S d, GlobalTheory.HL.MassGlue.finite_orbits S d⟩
