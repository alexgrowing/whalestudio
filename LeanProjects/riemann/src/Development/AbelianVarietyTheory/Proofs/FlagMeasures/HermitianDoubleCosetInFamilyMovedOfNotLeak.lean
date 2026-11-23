import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermLevelZeroAndBoundedRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovePreservesFrameLatticeLevelsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDefectClassMemTraceFirstFrameSpanStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingSecondTypeTestOnRepresentativesStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.OffLeak

theorem ncard_image_eq_of_iff {α β γ : Type*} (B : Set α) (f : α → β) (g : α → γ)
    (h : ∀ a ∈ B, ∀ b ∈ B, f a = f b ↔ g a = g b) : (f '' B).ncard = (g '' B).ncard := by
  classical
  refine Set.ncard_congr (fun c hc => g (Classical.choose ((Set.mem_image f B c).1 hc))) ?_ ?_ ?_
  · intro c hc
    exact ⟨_, (Classical.choose_spec ((Set.mem_image f B c).1 hc)).1, rfl⟩
  · intro c c' hc hc' hgg
    have e₁ := Classical.choose_spec ((Set.mem_image f B c).1 hc)
    have e₂ := Classical.choose_spec ((Set.mem_image f B c').1 hc')
    exact e₁.2.symm.trans (((h _ e₁.1 _ e₂.1).2 hgg).trans e₂.2)
  · rintro _ ⟨a, ha, rfl⟩
    have hfa : f a ∈ f '' B := ⟨a, ha, rfl⟩
    refine ⟨f a, hfa, ?_⟩
    have e := Classical.choose_spec ((Set.mem_image f B (f a)).1 hfa)
    exact (h _ e.1 _ ha).1 e.2

theorem coset_eq_iff {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (M : Submodule R V) (a b : V) :
    ({x | x - a ∈ M} : Set V) = {x | x - b ∈ M} ↔ a - b ∈ M := by
  constructor
  · intro h
    have ha : a ∈ ({x | x - a ∈ M} : Set V) := by simp
    rw [h] at ha
    exact ha
  · intro h
    ext x
    constructor
    · intro hx
      have hxb : (x - a) + (a - b) ∈ M := M.add_mem hx h
      have e : (x - a) + (a - b) = x - b := by abel
      rw [e] at hxb
      exact hxb
    · intro hx
      have hxa : (x - b) - (a - b) ∈ M := M.sub_mem hx h
      have e : (x - b) - (a - b) = x - a := by abel
      rw [e] at hxa
      exact hxa

theorem relIndex_eq_of_reps {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (M T B : Submodule R V)
    (hM : M ≤ T) (hB : B ≤ T) (h : ∀ y ∈ T, ∃ y₀ ∈ B, y - y₀ ∈ M) :
    M.toAddSubgroup.relIndex T.toAddSubgroup =
      (M.toAddSubgroup ⊓ B.toAddSubgroup).relIndex B.toAddSubgroup := by
  have hT : T.toAddSubgroup = B.toAddSubgroup ⊔ M.toAddSubgroup := by
    apply le_antisymm
    · intro y hy
      obtain ⟨y₀, hy₀, hm⟩ := h y hy
      have hs : y₀ + (y - y₀) ∈ B.toAddSubgroup ⊔ M.toAddSubgroup :=
        AddSubgroup.add_mem_sup hy₀ hm
      have e : y₀ + (y - y₀) = y := by abel
      rw [e] at hs
      exact hs
    · exact sup_le (fun x hx => hB hx) (fun x hx => hM hx)
  rw [hT, AddSubgroup.relIndex_sup_right, AddSubgroup.inf_relIndex_right]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem spanTo_mono {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V) {a b : ℕ}
    (h : a ≤ b) : S.spanTo g a ≤ S.spanTo g b := by
  unfold Frames.spanTo
  apply Submodule.span_mono
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, lt_of_lt_of_le hi h, rfl⟩

theorem th_ne_zero {L : LocE F E} {r k : ℕ} (S : Frames L r k) : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · intro h0
    apply S.ϖ_irr.ne_zero
    exact Subtype.ext h0
  · exact one_ne_zero
set_option maxHeartbeats 1000000 in

theorem inFF_moved_of_not_leak : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → (∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1) → ∀ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s → S.InFF β (j + 1) βJ d Λ₁ := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF x x' u s hMv hleak Λ₁ hΛ₁
  obtain ⟨hT₁, hY⟩ := GlobalTheory.T.hermitianMove_preserves_frameLattice_levels L r k S j β βJ d Λ hT hF x x' u s hMv Λ₁ hΛ₁
  have h78 := GlobalTheory.T.hermitianDefectClass_mem_trace_firstFrameSpan L r k S j β βJ d Λ hT hF x x' u s hMv hleak Λ₁ hΛ₁
  have h64 := GlobalTheory.T.termLevel_zero_and_bounded_representatives L r k S d Λ hT
  have h64₁ := GlobalTheory.T.termLevel_zero_and_bounded_representatives L r k S d Λ₁ hT₁
  have hMs : S.M d Λ ≤ S.sat Λ := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1
  have hMs₁ : S.M d Λ₁ ≤ S.sat Λ₁ := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ₁ hT₁).2.2.1
  unfold Frames.InFF at hF ⊢
  obtain ⟨hTB, hbe, hle, ⟨z, hz, hzJ⟩, hn⟩ := hF
  unfold Frames.TypeBe at hTB
  obtain ⟨Y, hYdef⟩ : ∃ Y : Submodule E S.V, Y = S.spanTo S.f (↑j + 1) ⊔ S.spanTo S.f' (↑j + 1) :=
    ⟨_, rfl⟩
  have hYmem : ∀ y, y ∈ Y ↔ y ∈ S.spanTo S.f (↑j + 1) ⊔ S.spanTo S.f' (↑j + 1) := by
    intro y
    rw [hYdef]
  have hjr : (j : ℕ) + 1 ≤ r := j.isLt
  have hjr' : (j : ℕ) + 1 ≤ r + 1 := by omega
  have hYME : Y ≤ S.ME := by
    rw [hYdef]
    exact sup_le_sup (spanTo_mono S S.f hjr') (spanTo_mono S S.f' hjr')
  have hYX : Y ≤ S.X ⊔ S.X' := by
    rw [hYdef]
    exact sup_le_sup (spanTo_mono S S.f hjr) (spanTo_mono S S.f' hjr)
  have hYY : ∀ y ∈ Y, (y ∈ Λ → y ∈ Λ₁) ∧ (y ∈ S.M d Λ₁ ↔ y ∈ S.M d Λ) ∧
      S.lev (S.fr d Λ₁) (S.fr' d Λ₁) y = S.lev (S.fr d Λ) (S.fr' d Λ) y :=
    fun y hy => hY y ((hYmem y).1 hy)
  have memSat : ∀ (Λ' : Submodule L.O S.V) (y : S.V), y ∈ S.sat Λ' ↔ y ∈ Λ' ∧ y ∈ S.ME := by
    intro Λ' y
    unfold Frames.sat
    simp [Submodule.mem_inf]
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : Submodule L.O S.V, ∀ y, y ∈ B₀ ↔ y ∈ Λ ∧ y ∈ Y :=
    ⟨Λ ⊓ Y.restrictScalars L.O, fun y => by simp [Submodule.mem_inf]⟩
  have hB₀Y : ∀ y ∈ B₀, y ∈ Y := fun y hy => ((hB₀ y).1 hy).2
  have hB₀sat : ∀ y ∈ B₀, y ∈ S.sat Λ := fun y hy =>
    (memSat Λ y).2 ⟨((hB₀ y).1 hy).1, hYME (hB₀Y y hy)⟩
  have hB₀Λ₁ : ∀ y ∈ B₀, y ∈ Λ₁ := fun y hy => (hYY y (hB₀Y y hy)).1 ((hB₀ y).1 hy).1
  have hB₀sat₁ : ∀ y ∈ B₀, y ∈ S.sat Λ₁ := fun y hy =>
    (memSat Λ₁ y).2 ⟨hB₀Λ₁ y hy, hYME (hB₀Y y hy)⟩
  have hMiff : ∀ y ∈ B₀, (y ∈ S.M d Λ₁ ↔ y ∈ S.M d Λ) := fun y hy => (hYY y (hB₀Y y hy)).2.1
  have hlev : ∀ y ∈ B₀, S.levC d Λ₁ y = S.levC d Λ y := by
    intro y hy
    unfold Frames.levC
    exact (hYY _ (Y.smul_mem _ (hB₀Y y hy))).2.2

  have rep : ∀ y ∈ S.sat Λ, ∃ y₁ ∈ B₀, y - y₁ ∈ S.M d Λ := by
    intro y hy
    obtain ⟨y₁, hy₁Y, hm⟩ := (h64.2.1 y hy (↑j + 1)).1 (hle y hy)
    have hs : y - (y - y₁) ∈ S.sat Λ := (S.sat Λ).sub_mem hy (hMs hm)
    have e : y - (y - y₁) = y₁ := by abel
    rw [e] at hs
    exact ⟨y₁, (hB₀ y₁).2 ⟨((memSat Λ y₁).1 hs).1, (hYmem y₁).2 hy₁Y⟩, hm⟩

  have rep₁ : ∀ y ∈ S.sat Λ₁, ∃ y₀ ∈ B₀, y - y₀ ∈ S.M d Λ₁ := by
    intro y hy
    obtain ⟨y₀, h1, h2, h3⟩ := h78 y hy
    exact ⟨y₀, (hB₀ y₀).2 ⟨h1, (hYmem y₀).2 h2⟩, h3⟩

  have hinv : ∀ (Λ' : Submodule L.O S.V), S.IsTerm d Λ' → ∀ y ∈ S.sat Λ', ∀ y₁,
      y - y₁ ∈ S.M d Λ' → S.levC d Λ' y₁ = S.levC d Λ' y := by
    intro Λ' hT' y hy y₁ hm
    have hm' : -(y - y₁) ∈ S.M d Λ' := (S.M d Λ').neg_mem hm
    have e₁ : -(y - y₁) = y₁ - y := by abel
    rw [e₁] at hm'
    have hc := (GlobalTheory.T.termLevel_zero_and_bounded_representatives L r k S d Λ' hT').2.2.1 y hy (y₁ - y) hm'
    have e₂ : y + (y₁ - y) = y₁ := by abel
    rw [e₂] at hc
    exact hc

  have hbe₁ : S.be d Λ₁ = S.be d Λ := by
    unfold Frames.be
    rw [relIndex_eq_of_reps (S.M d Λ₁) (S.sat Λ₁) B₀ hMs₁ (fun y hy => hB₀sat₁ y hy) rep₁,
      relIndex_eq_of_reps (S.M d Λ) (S.sat Λ) B₀ hMs (fun y hy => hB₀sat y hy) rep]
    congr 1
    ext y
    simp only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup]
    exact ⟨fun h => ⟨(hMiff y h.2).1 h.1, h.2⟩, fun h => ⟨(hMiff y h.2).2 h.1, h.2⟩⟩

  have hth : S.th ≠ 0 := th_ne_zero S
  have hInTh : ∀ w : S.V, algebraMap F E S.th⁻¹ • w ∈ (B₀ : Set S.V) → S.InTh Λ w := by
    intro w hw
    refine ⟨_, ((hB₀ _).1 hw).1, ?_⟩
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ hth, map_one, one_smul]
  have hnotBB : ¬ S.BBzero d Λ₁ := by
    intro hbb
    apply hTB.1
    unfold Frames.BBzero at hbb ⊢
    refine le_antisymm hMs ?_
    intro y hy
    obtain ⟨y₁, hy₁, hm⟩ := rep y hy
    have h1 : y₁ ∈ S.M d Λ₁ := by
      rw [hbb]
      exact hB₀sat₁ y₁ hy₁
    have h2 : (y - y₁) + y₁ ∈ S.M d Λ := (S.M d Λ).add_mem hm ((hMiff y₁ hy₁).1 h1)
    have e : (y - y₁) + y₁ = y := by abel
    rw [e] at h2
    exact h2
  have hTB₁ : S.TypeBe d Λ₁ :=
    GlobalTheory.T.pairing_second_type_test_on_representatives L r k S d Λ₁ hT₁ hnotBB (B₀ : Set S.V)
      (fun y hy => ⟨hB₀Λ₁ y hy, hYX (hB₀Y y hy)⟩) rep₁
      (fun x₁ hx₁ x₁' hx₁' x₂ hx₂ x₂' hx₂' h1 h2 =>
        hTB.2.2 x₁ hx₁ x₁' hx₁' x₂ hx₂ x₂' hx₂' (hInTh _ h1) (hInTh _ h2))

  have hle₁ : ∀ y ∈ S.sat Λ₁, S.levC d Λ₁ y ≤ ↑j + 1 := by
    intro y hy
    obtain ⟨y₀, hy₀, hm⟩ := rep₁ y hy
    have hy0 : y₀ ∈ S.spanTo S.f (↑j + 1) ⊔ S.spanTo S.f' (↑j + 1) := (hYmem y₀).1 (hB₀Y y₀ hy₀)
    have key := (h64₁.2.1 y hy (↑j + 1)).2
    have ex : ∃ y₁ ∈ S.spanTo S.f (↑j + 1) ⊔ S.spanTo S.f' (↑j + 1), y - y₁ ∈ S.M d Λ₁ :=
      ⟨y₀, hy0, hm⟩
    exact key ex
  have hex₁ : ∃ y ∈ S.sat Λ₁, S.levC d Λ₁ y = ↑j + 1 := by
    obtain ⟨y₁, hy₁, hm⟩ := rep z hz
    refine ⟨y₁, hB₀sat₁ y₁ hy₁, ?_⟩
    rw [hlev y₁ hy₁, hinv Λ hT z hz y₁ hm, hzJ]

  have hset : ∀ (Λ' : Submodule L.O S.V), S.IsTerm d Λ' → (∀ y ∈ B₀, y ∈ S.sat Λ') →
      (∀ y ∈ S.sat Λ', ∃ y₀ ∈ B₀, y - y₀ ∈ S.M d Λ') →
      {C : Set S.V | ∃ y ∈ S.sat Λ', S.levC d Λ' y = ↑j + 1 ∧ C = {x | x - y ∈ S.M d Λ'}} =
        (fun y => {x | x - y ∈ S.M d Λ'}) '' {y | y ∈ B₀ ∧ S.levC d Λ' y = ↑j + 1} := by
    intro Λ' hT' hBs hrep
    ext C
    constructor
    · rintro ⟨y, hy, hyJ, rfl⟩
      obtain ⟨y₀, hy₀, hm⟩ := hrep y hy
      refine ⟨y₀, ⟨hy₀, (hinv Λ' hT' y hy y₀ hm).trans hyJ⟩, ?_⟩
      have hm' : -(y - y₀) ∈ S.M d Λ' := (S.M d Λ').neg_mem hm
      have e : -(y - y₀) = y₀ - y := by abel
      rw [e] at hm'
      exact (coset_eq_iff (S.M d Λ') y₀ y).2 hm'
    · rintro ⟨y, ⟨hy, hyJ⟩, rfl⟩
      exact ⟨y, hBs y hy, hyJ, rfl⟩
  have hn₁ : S.nLev d Λ₁ (↑j + 1) = βJ := by
    rw [← hn]
    unfold Frames.nLev
    rw [hset Λ₁ hT₁ hB₀sat₁ rep₁, hset Λ hT hB₀sat rep]
    have hBB : {y | y ∈ B₀ ∧ S.levC d Λ₁ y = ↑j + 1} = {y | y ∈ B₀ ∧ S.levC d Λ y = ↑j + 1} := by
      ext y
      exact ⟨fun h => ⟨h.1, (hlev y h.1).symm.trans h.2⟩, fun h => ⟨h.1, (hlev y h.1).trans h.2⟩⟩
    rw [hBB]
    apply ncard_image_eq_of_iff
    intro a ha b hb
    have hab : a - b ∈ Y := Y.sub_mem (hB₀Y a ha.1) (hB₀Y b hb.1)
    exact (coset_eq_iff (S.M d Λ₁) a b).trans ((hYY _ hab).2.1.trans (coset_eq_iff (S.M d Λ) a b).symm)
  exact ⟨hTB₁, hbe₁.trans hbe, hle₁, hex₁, hn₁⟩

end GlobalTheory.HL.OffLeak
