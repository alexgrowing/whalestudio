import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking

noncomputable section

namespace GlobalTheory.Fc

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top

theorem eventuallyAllScaleContexts_and_of_both {p q : Ctx → Prop} (hp : Ev p) (hq : Ev q) : Ev fun K => p K ∧ q K := by
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  refine ⟨min a b, lt_min ha hb, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he (hle.trans (min_le_left _ _)) h52 h8
  obtain ⟨K', hK'⟩ := hq e C8 he (hle.trans (min_le_right _ _)) h52 h8
  refine ⟨K.sup K', fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 (large_of_sup hL).1
  obtain ⟨b1, hb1⟩ := hK' C hC hC8 (large_of_sup hL).2
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  exact ⟨max a3 b3, fun X h1 h2 h3 h4 hx =>
    ⟨ha3 X h1 h2 h3 h4 (le_trans (le_max_left _ _) hx), hb3 X h1 h2 h3 h4 (le_trans (le_max_right _ _) hx)⟩⟩

theorem eventuallyAllScaleContexts_mono_of_imp {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h1 h2 h3 h4 hx => h X (ha3 X h1 h2 h3 h4 hx)⟩

def sAnd (Q R : V4.Slot) : V4.Slot := fun K X f T c => Q K X f T c ∧ R K X f T c

def LargeBaseCondition (KP : ∀ B : Base, Fr B.toPre → Prop) (Q R : V4.Slot) : Prop :=
  EvLg fun K B f T => KP B f → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c → R K ⟨B, C, W, V, S, N, G⟩ f T c

variable {KP : ∀ B : Base, Fr B.toPre → Prop} {Q Q' R R' : V4.Slot} {Bd : BdT} {Lk : LkT Bd}

theorem LargeBaseCondition.and (h : LargeBaseCondition KP Q R) (h' : LargeBaseCondition KP Q R') : LargeBaseCondition KP Q (sAnd R R') :=
  eventuallyAllScaleContexts_mono_of_imp (fun _ H => (H.1.inter H.2).imp fun _ _ _ _ t k C W V S N G c q => ⟨t.1 k C W V S N G c q, t.2 k C W V S N G c q⟩)
    (eventuallyAllScaleContexts_and_of_both h h')

theorem LargeBaseCondition.passes (h : LargeBaseCondition KP Q R) (h1 : V4.ExTrue KP Q) (h2 : V4.Export Q) (h3 : V4.Retwist Q Q') :
    V4.ExTrue KP (sAnd Q R) ∧ V4.Export (sAnd Q R) ∧ V4.Retwist (sAnd Q R) (sAnd Q' R) := by
  refine ⟨eventuallyAllScaleContexts_mono_of_imp ?_ (eventuallyAllScaleContexts_and_of_both h h1), eventuallyAllScaleContexts_mono_of_imp (fun _ H X f T c q => H X f T c q.1) h2, eventuallyAllScaleContexts_mono_of_imp ?_ h3⟩
  · intro K H
    refine (H.1.inter H.2).imp ?_
    intro B f T _ t k
    obtain ⟨C, W, V, S, N, G, c, q⟩ := t.2 k
    exact ⟨C, W, V, S, N, G, c, q, t.1 k C W V S N G c q⟩
  · intro K H X f T c q e A S₂ a
    obtain ⟨B', f', T', a1, a2, a3, a4, a5, a6⟩ := H X f T c q.1 e A S₂ a
    exact ⟨B', f', T', a1, a2, a3, a4, a5, fun C W V S N G c' q' =>
      ⟨(a6 C W V S N G c' q'.1).1, (a6 C W V S N G c' q'.1).2, q'.2⟩⟩

variable (KP Q Q' Lk) in

def RowL (H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop) : Prop := ∃ R : V4.Slot, LargeBaseCondition KP Q R ∧ Row (sAnd Q' R) Lk H

variable (KP Q Q' Lk) in

def ExBL : Prop := ∃ R : V4.Slot, LargeBaseCondition KP Q R ∧ ExB (sAnd Q' R) Lk

theorem Row.strengthen {H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (hQ : ∀ K X f T c, Q K X f T c → Q' K X f T c) (h : Row Q' Lk H) :
    Row Q Lk H := Row.map (fun _ _ _ b => b) hQ (fun _ _ _ _ _ t => t) h

theorem RowL.and {H H' : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (h : RowL KP Q Q' Lk H) (h' : RowL KP Q Q' Lk H') :
    RowL KP Q Q' Lk fun 𝒜 σ => H 𝒜 σ ∧ H' 𝒜 σ := by
  obtain ⟨R, r, h⟩ := h
  obtain ⟨R', r', h'⟩ := h'
  exact ⟨_, r.and r', (h.strengthen fun _ _ _ _ _ t => ⟨t.1, t.2.1⟩).and (h'.strengthen fun _ _ _ _ _ t => ⟨t.1, t.2.2⟩)⟩

theorem RowL.elim {H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (hx : ExBL KP Q Q' Lk) (h : RowL KP Q Q' Lk H) :
    ∃ R : V4.Slot, LargeBaseCondition KP Q R ∧ ExB (sAnd Q' R) Lk ∧ Row (sAnd Q' R) Lk H := by
  obtain ⟨R, r, hx⟩ := hx
  obtain ⟨R', r', h⟩ := h
  exact ⟨_, r.and r', EvP.mono (fun _ _ _ H β q => H β ⟨q.1, q.2.1⟩) hx, h.strengthen fun _ _ _ _ _ t => ⟨t.1, t.2.2⟩⟩

theorem Row.rowL {H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (r : LargeBaseCondition KP Q R) (h : Row Q' Lk H) : RowL KP Q Q' Lk H :=
  ⟨R, r, h.strengthen fun _ _ _ _ _ t => t.1⟩

theorem largeBaseProperty_true : LargeBaseCondition KP Q fun _ _ _ _ _ => True :=
  ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ =>
    ⟨0, fun _ _ _ _ _ _ => ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial⟩⟩⟩⟩⟩⟩

end GlobalTheory.Fc

end
