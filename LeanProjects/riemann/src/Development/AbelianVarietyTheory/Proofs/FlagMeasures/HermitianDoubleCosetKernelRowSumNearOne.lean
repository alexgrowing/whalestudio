import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetInFamilyMovedOfNotLeakStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMoveTermWeightCharacterStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralLinearPositiveNormBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermDoubleCosetMovesFiniteTargetsSplitStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovesTotalMeasureEstimatesStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ}
  (S : _root_.GlobalTheory.HL.Frames L r k) in
private theorem cK_nonneg' (β βJ : ℕ) :
    0 ≤ S.cK β βJ := by
  unfold _root_.GlobalTheory.HL.Frames.cK
  positivity

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem ind_eq_one_of_pos {W : Type} {P : W → Prop} {w : W} (h : P w) :
    _root_.GlobalTheory.IdxInt.ind P w = 1 := by
  unfold _root_.GlobalTheory.IdxInt.ind
  exact if_pos h

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem ind_eq_zero_of_not {W : Type} {P : W → Prop} {w : W} (h : ¬ P w) :
    _root_.GlobalTheory.IdxInt.ind P w = 0 := by
  unfold _root_.GlobalTheory.IdxInt.ind
  exact if_neg h

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ}
  (S : _root_.GlobalTheory.HL.Frames L r k) in
private theorem eq_of_MvTo_of_MvTo {a : ℕ} {d : S.Datum}
    {Λ Λ₁ Λ₂ : Submodule L.O S.V} {w : S.MW}
    (h₁ : S.MvTo a d Λ Λ₁ w) (h₂ : S.MvTo a d Λ Λ₂ w) : Λ₁ = Λ₂ := by
  unfold _root_.GlobalTheory.HL.Frames.MvTo at h₁ h₂
  exact SetLike.coe_injective (h₁.2.trans h₂.2.symm)

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ}
  (S : _root_.GlobalTheory.HL.Frames L r k) in
private theorem Mv_of_MvTo {a : ℕ} {d : S.Datum}
    {Λ Λ₁ : Submodule L.O S.V} {w : S.MW}
    (h : S.MvTo a d Λ Λ₁ w) : S.Mv a d Λ w := by
  unfold _root_.GlobalTheory.HL.Frames.MvTo at h
  exact h.1

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ}
  (S : _root_.GlobalTheory.HL.Frames L r k) in
private theorem exists_MvTo_isTerm_of_Mv_of_InFF [IsNonarchimedeanLocalField F] [CharZero F]
    (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V)
    (hT : S.IsTerm d Λ) (hF : S.InFF β (j + 1) βJ d Λ)
    (w : S.MW) (hw : S.Mv (j + 1) d Λ w) :
    ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ S.IsTerm d Λ₁ := by
  have hw' := hw
  unfold _root_.GlobalTheory.HL.Frames.Mv at hw'
  obtain ⟨n₀, -, n₀', -, n'', -, -, -, -, -, hmov, hW⟩ :=
    _root_.GlobalTheory.HL.MoveWit.main L r k S j β βJ d Λ hT hF _ _ _ _ hw'
  refine ⟨n₀⁻¹ • Λ, ?_, ?_⟩
  · unfold _root_.GlobalTheory.HL.Frames.MvTo
    exact ⟨hw, hmov⟩
  · unfold _root_.GlobalTheory.HL.Frames.IsTerm
    exact ⟨⟨_, _⟩, hW⟩

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in

theorem _root_.GlobalTheory.HL.kern_row_sum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → |(∑ᶠ y : {y // S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y}, S.kern β (j + 1) βJ d Λ y) - 1| ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk j β βJ d Λ hT hF
  obtain ⟨-, -, hfinK, -, hsplit⟩ :=
    _root_.GlobalTheory.HL.moves_split_by_target L r k S j β βJ d Λ hT hF
  obtain ⟨hNMv, hNLeak, -, hI, hIleak, -⟩ :=
    _root_.GlobalTheory.HL.MoveTotal.total_moves L r k S hk j β βJ d Λ hT hF
  have hlin := _root_.GlobalTheory.IdxInt.Lin.main (S.refA (↑j + 1) Λ)
  have hc := cK_nonneg' S β βJ
  set Good : S.MW → Prop := fun w => ∃ Λ₁, S.MvTo (↑j + 1) d Λ Λ₁ w ∧
    (S.IsTerm d Λ₁ ∧ S.InFF β (↑j + 1) βJ d Λ₁) with hGood
  obtain ⟨hNG, hsum⟩ := hsplit
    (fun y => S.IsTerm d y ∧ S.InFF β (↑j + 1) βJ d y)
    (fun _ => 1) (_root_.GlobalTheory.IdxInt.ind Good)
    (fun w Λ₁ h => by
      by_cases hP : S.IsTerm d Λ₁ ∧ S.InFF β (↑j + 1) βJ d Λ₁
      · rw [if_pos hP, ind_eq_one_of_pos ⟨Λ₁, h, hP⟩]
      · rw [if_neg hP, ind_eq_zero_of_not]
        rintro ⟨Λ₂, h₂, hP₂⟩
        exact hP (eq_of_MvTo_of_MvTo S h₂ h ▸ hP₂))
    (fun w hw => ind_eq_zero_of_not fun ⟨Λ₁, h, _⟩ =>
      hw (Mv_of_MvTo S h))
  have hsupp : (Function.support fun y : {y // S.IsTerm d y ∧
      S.InFF β (↑j + 1) βJ d y} =>
        S.kern β (↑j + 1) βJ d Λ ↑y).Finite :=
    (hfinK.preimage Subtype.val_injective.injOn).subset fun y hy => hy
  have hK : (((∑ᶠ y : {y // S.IsTerm d y ∧
      S.InFF β (↑j + 1) βJ d y},
        S.kern β (↑j + 1) βJ d Λ ↑y : ℝ)) : ℂ) =
      (S.cK β βJ : ℂ) *
        _root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ)
          (_root_.GlobalTheory.IdxInt.ind Good) := by
    have hmap := map_finsum Complex.ofRealHom hsupp
    simp only [Complex.ofRealHom_eq_coe] at hmap
    rw [hmap, ← hsum]
    simp
  set H : S.MW → ℂ := fun w =>
    _root_.GlobalTheory.IdxInt.ind (S.Mv (↑j + 1) d Λ) w +
      (-1) * _root_.GlobalTheory.IdxInt.ind Good w with hH
  have hNH : _root_.GlobalTheory.IdxInt.Nice (S.refA (↑j + 1) Λ) H :=
    (hlin.1 _ _ hNMv (hlin.2.1 (-1) _ hNG).1).1
  have hIH : _root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ) H =
      _root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ)
          (_root_.GlobalTheory.IdxInt.ind (S.Mv (↑j + 1) d Λ)) +
        (-1) * _root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ)
          (_root_.GlobalTheory.IdxInt.ind Good) := by
    rw [← (hlin.2.1 (-1) _ hNG).2]
    exact (hlin.1 _ _ hNMv (hlin.2.1 (-1) _ hNG).1).2.1
  have hbound : ∀ w, ‖H w‖ ≤ (_root_.GlobalTheory.IdxInt.ind
      (fun w => S.Mv (↑j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1) w).re := by
    intro w
    by_cases hw : S.Mv (↑j + 1) d Λ w
    · by_cases hg : Good w
      · rw [hH]
        simp only
        rw [ind_eq_one_of_pos hw, ind_eq_one_of_pos hg]
        unfold _root_.GlobalTheory.IdxInt.ind
        split_ifs <;> simp
      · have hleak : ¬ S.NoLeak Λ w.2.1 := by
          intro hno
          apply hg
          obtain ⟨Λ₁, h₁, hT₁⟩ := exists_MvTo_isTerm_of_Mv_of_InFF S j β βJ d Λ hT hF w hw
          refine ⟨Λ₁, h₁, hT₁, ?_⟩
          have hw' := hw
          unfold _root_.GlobalTheory.HL.Frames.Mv at hw'
          have h₁' := h₁
          unfold _root_.GlobalTheory.HL.Frames.MvTo at h₁'
          unfold _root_.GlobalTheory.HL.Frames.NoLeak at hno
          exact _root_.GlobalTheory.HL.OffLeak.inFF_moved_of_not_leak L r k S j β βJ d Λ hT hF _ _ _ _
            hw' hno Λ₁ h₁'.2
        rw [hH]
        simp only
        rw [ind_eq_one_of_pos hw, ind_eq_zero_of_not hg, ind_eq_one_of_pos ⟨hw, hleak⟩]
        simp
    · have hg : ¬ Good w := fun ⟨Λ₁, h, _⟩ => hw (Mv_of_MvTo S h)
      rw [hH]
      simp only
      rw [ind_eq_zero_of_not hw, ind_eq_zero_of_not hg]
      unfold _root_.GlobalTheory.IdxInt.ind
      split_ifs <;> simp
  have hnorm := (hlin.1 _ _ hNH hNLeak).2.2 hbound
  have hKre := congrArg Complex.re hK
  rw [Complex.ofReal_re, Complex.re_ofReal_mul] at hKre
  have hsplitre := congrArg Complex.re hIH
  simp only [Complex.add_re, neg_one_mul, Complex.neg_re] at hsplitre
  have hHre : |S.cK β βJ *
      (_root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ) H).re| ≤
      16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
    rw [abs_mul, abs_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hc).trans
      ((mul_le_mul_of_nonneg_left hnorm hc).trans hIleak)
  rw [hKre]
  rw [hsplitre] at hHre
  rw [abs_le] at hI hHre ⊢
  constructor <;> nlinarith [hI.1, hI.2, hHre.1, hHre.2]

end GlobalTheory.HL
