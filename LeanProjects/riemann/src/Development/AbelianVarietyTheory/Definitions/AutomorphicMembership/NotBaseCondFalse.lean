import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RecExGOfRecAtG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpreadLamOfLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToMapSurj

noncomputable section

namespace GlobalTheory.Mem.Top.GroupRetwisting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

abbrev BaseP : Type 1 := ∀ B : Base, Fr B.toPre → Prop

structure BaseCond (KP : BaseP) : Prop where
  ex : EvG fun K => ∃ (P : Pre) (f₀ : Fr P), K.Over P ∧ ∀ (S₁ : IntermediateField ℚ ℂ → Finset ℂ)
    (S₂ : IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Finset ℂ), (∀ F, ∀ z ∈ S₁ F, IsAlgebraic ℚ z) →
    (∀ F F₀, ∀ z ∈ S₂ F F₀, IsAlgebraic ℚ z) →
    ∃ (B : Base) (f : Fr B.toPre), B.toPre = P ∧ HEq f f₀ ∧ KP B f ∧ Has₂ B (S₁ B.KsC) (S₂ B.KsC B.fixedCoefficientFieldInComplex)
  enl : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre), Enl B B' → HEq f' f → KP B f → KP B' f'

def ExTrueG (KP : BaseP) (Q : V4.Slot) : Prop :=
  EvLgG fun K B f T => KP B f → ∃ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c

def ExportG (Q : V4.Slot) : Prop :=
  EvG fun K => ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T), Q K X f T c → ExportAt X.toD7 c.O.nch c.O.xd

def RetwistG (Q Q' : V4.Slot) : Prop :=
  EvG fun K => ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T), Q K X f T c → ExportAt X.toD7 c.O.nch c.O.xd →
    ∀ (A : ℕ → Finset ℕ) (S₂ : ∀ B : Pre, Fr B → Set (HChar B.host.E) → Finset ℂ), (∀ B f Ξ, ∀ z ∈ S₂ B f Ξ, IsAlgebraic ℚ z) →
      ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B'), Enl X.B B' ∧ HEq f' f ∧ T'.pl = T.pl ∧ T'.Avoids A ∧
        (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧
        ∀ (C : Cols B') (W : RowsRest B' C) (V : DivStage B' C W) (S : SStage B' C W) (N : NStage B' C W) (G : GJStage B' C)
          (c' : V4.Core K ⟨B', C, W, V, S, N, G⟩ f' T'), Q K ⟨B', C, W, V, S, N, G⟩ f' T' c' →
          DQ.TwAllAt (assemble B' C W V S N G) c'.O.nch c'.O.xd ∧ Q' K ⟨B', C, W, V, S, N, G⟩ f' T' c'

def FromCoreAt (Q : V4.Slot) (K : Ctx) (D : D7) (Y : Lay D) : Prop :=
  ∃ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T), Q K X f T c ∧
    (⟨D, layObj Y⟩ : Σ D : D7, Obj2 D) = ⟨X.toD7, c.O⟩

def Forced (K : Ctx) (B : Base) (T : TwDat B) : Prop :=
  ∀ p : ℕ, p.Prime → ((∃ i, p = B.host.g i) ∨ p = B.host.d ∨ (p : ℝ) ≤ K.s.X'' B.R.n) → p ∈ T.pl

abbrev AtP : Type 1 := ∀ (_ : Ctx) (B : Base), Fr B.toPre → TwDat B → Prop

def Step (KP : BaseP) (p q : AtP) : Prop := EvLgG fun K B f T => KP B f → Forced K B T → p K B f T → q K B f T

def HasCore (Q : V4.Slot) : AtP := fun K B f T =>
  ∃ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c

def FirstG (KP : BaseP) (Q : V4.Slot) : Prop := Step KP (fun _ B _ T => T = TwDat.untw B T.pl) (HasCore Q)

def ExportF (KP : BaseP) (Q : V4.Slot) : Prop :=
  EvLgG fun K B f T => KP B f → T = TwDat.untw B T.pl → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
    (N : NStage B C W) (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c →
    ExportAt (assemble B C W V S N G) c.O.nch c.O.xd

def Pass (KP : BaseP) (Q : V4.Slot) (r : AtP) : Prop :=
  EvLgG fun K B f T => KP B f → T = TwDat.untw B T.pl → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
    (N : NStage B C W) (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c →
    ExportAt (assemble B C W V S N G) c.O.nch c.O.xd →
    ∀ (A : ℕ → Finset ℕ) (S₂ : ∀ P : Pre, Fr P → Set (HChar P.host.E) → Finset ℂ), (∀ P g Ξ, ∀ z ∈ S₂ P g Ξ, IsAlgebraic ℚ z) →
      ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B'), Enl B B' ∧ HEq f' f ∧ T'.pl = T.pl ∧ T'.Avoids A ∧
        (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧ r K B' f' T'

def SecondG (KP : BaseP) (Q Q' : V4.Slot) : Prop :=
  Pass KP Q (HasCore fun K X f T c => Q K X f T c ∧ DQ.TwAllAt X.toD7 c.O.nch c.O.xd ∧ Q' K X f T c)

def RetwistA (KP : BaseP) (admitted : AtP) (Q Q' : V4.Slot) : Prop :=
  Pass KP Q fun K B f T => admitted K B f T ∧ ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c →
    DQ.TwAllAt (assemble B C W V S N G) c.O.nch c.O.xd ∧ Q' K ⟨B, C, W, V, S, N, G⟩ f T c

def LargeBaseConditionG (KP : BaseP) (Q R : V4.Slot) : Prop :=
  EvLgG fun K B f T => KP B f → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c → R K ⟨B, C, W, V, S, N, G⟩ f T c

theorem evG_all {p : Ctx → Prop} (h : ∀ K, p K) : EvG p := evG_good.imp fun K _ _ _ _ _ => h K

theorem fromCore_iff (Q : V4.Slot) (D : D7) (Y : Lay D) : V4.FromCore Q D Y ↔ ∃ K, FromCoreAt Q K D Y := Iff.rfl

theorem exTrueG_of {KP : BaseP} {Q : V4.Slot} (h : V4.ExTrue KP Q) : ExTrueG KP Q := evG_of_ev h
theorem exportG_of {Q : V4.Slot} (h : V4.Export Q) : ExportG Q := evG_of_ev h
theorem retwistG_of {Q Q' : V4.Slot} (h : V4.Retwist Q Q') : RetwistG Q Q' := evG_of_ev h

theorem baseCond_of {KP : BaseP} (h : V4.KsCond KP) {PP : ∀ P : Pre, Fr P → Prop}
    (hP : EvG fun K => ∃ (P : Pre) (f : Fr P), K.Over P ∧ PP P f) : BaseCond fun B f => KP B f ∧ PP B.toPre f := by
  refine ⟨((evG_of_ev h.ex).inter hP).imp ?_, fun B B' f f' e hf hk => ⟨h.enl B B' f f' e hf hk.1, ?_⟩⟩
  · rintro K _ _ _ _ ⟨hk, P, f₀, hO, hp⟩
    obtain ⟨B₀, rfl, -⟩ := BaseExt.exists_base P ∅ ∅ ∅ (by simp) (by simp) (by simp)
    refine ⟨_, f₀, hO, fun S₁ S₂ a₁ a₂ => ?_⟩
    obtain ⟨B, f, e, hf, k, H⟩ := hk B₀ f₀ S₁ S₂ hO a₁ a₂
    refine ⟨B, f, e, hf, ⟨k, ?_⟩, H⟩
    generalize B₀.toPre = P₀ at *
    subst e
    cases hf
    exact hp
  · have e1 := e.1
    have h2 := hk.2
    clear hk e
    generalize B.toPre = P at *
    generalize B'.toPre = P' at *
    subst e1
    cases hf
    exact h2

theorem lg_forced (K : Ctx) : large₂ K fun B _ T => Forced K B T := by
  have h : ∀ P : Pre, ∃ S : Finset ℕ,
      ∀ p : ℕ, p.Prime → ((∃ i, p = P.host.g i) ∨ p = P.host.d ∨ (p : ℝ) ≤ K.s.X'' P.R.n) → p ∈ S := fun P => by
    refine ⟨{P.host.g 0, P.host.g 1, P.host.d} ∪ Finset.range (⌊K.s.X'' P.R.n⌋₊ + 1), ?_⟩
    rintro p - (⟨i, rfl⟩ | rfl | h)
    · fin_cases i <;> simp
    · simp
    · exact Finset.mem_union_right _ (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor h)))
  choose S hS using h
  exact ⟨fun _ _ _ => ∅, fun P _ _ _ => S P, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
    fun B _ _ _ _ h _ p hp h' => h (hS _ p hp h')⟩

theorem lg_all (K : Ctx) {p : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ B f T, K.Over B.toPre → p B f T) : large₂ K p :=
  (lg_forced K).imp fun B f T hO _ => h B f T hO

section Steps
variable {KP : BaseP} {p q r : AtP}

theorem Step.of_evG (h : EvG fun K => ∀ B f T, K.Over B.toPre → KP B f → Forced K B T → p K B f T → q K B f T) : Step KP p q :=
  EvG.imp h fun K _ _ _ _ H => lg_all K H

theorem Step.of_all (h : ∀ K B f T, K.Over B.toPre → KP B f → Forced K B T → p K B f T → q K B f T) : Step KP p q :=
  Step.of_evG (evG_all h)

theorem Step.trans (h : Step KP p q) (h' : Step KP q r) : Step KP p r :=
  (EvG.inter h h').imp fun _ _ _ _ _ H => (H.1.inter H.2).imp fun _ _ _ _ G a b c => G.2 a b (G.1 a b c)

theorem Step.and (h : Step KP p q) (h' : Step KP p r) : Step KP p fun K B f T => q K B f T ∧ r K B f T :=
  (EvG.inter h h').imp fun _ _ _ _ _ H => (H.1.inter H.2).imp fun _ _ _ _ G a b c => ⟨G.1 a b c, G.2 a b c⟩

theorem Step.of_evLgG (h : EvLgG q) : Step KP p q := EvG.imp h fun _ _ _ _ _ H => H.imp fun _ _ _ _ G _ _ _ => G

theorem exTrueG_iff_step {Q : V4.Slot} : ExTrueG KP Q ↔ Step KP (fun _ _ _ _ => True) (HasCore Q) :=
  ⟨fun h => EvG.imp h fun _ _ _ _ _ H => H.imp fun _ _ _ _ G a _ _ => G a,
    fun h => EvG.imp h fun K _ _ _ _ H => (H.inter (lg_forced K)).imp fun _ _ _ _ G a => G.1 a G.2 trivial⟩

theorem firstG_of {Q : V4.Slot} (h : ExTrueG KP Q) : FirstG KP Q :=
  (Step.of_all fun _ _ _ _ _ _ _ _ => trivial).trans (exTrueG_iff_step.1 h)

theorem exportF_of {Q : V4.Slot} (h : ExportG Q) : ExportF KP Q :=
  EvG.imp h fun K _ _ _ _ H => lg_all K fun B f T _ _ _ C W V S N G c q => H ⟨B, C, W, V, S, N, G⟩ f T c q

theorem retwistA_of {Q Q' : V4.Slot} (h : RetwistG Q Q') : RetwistA KP (fun _ _ _ _ => True) Q Q' :=
  EvG.imp h fun K _ _ _ _ H => lg_all K fun B f T _ _ _ C W V S N G c q e A S₂ a =>
    let ⟨B', f', T', a1, a2, a3, a4, a5, a6⟩ := H ⟨B, C, W, V, S, N, G⟩ f T c q e A S₂ a
    ⟨B', f', T', a1, a2, a3, a4, a5, trivial, a6⟩

end Steps

theorem lg_of_lgOn {Δ : Pre → Type} {Sm : ∀ B : Pre, Fr B → Δ B → IntermediateField ℚ ℂ → Prop} {K : Ctx}
    {p : ∀ B : Base, Fr B.toPre → Δ B.toPre → TwDat B → Prop} (h : LgOn Sm K p) :
    large₂ K fun B f T => (∃ δ, Sm B.toPre f δ B.KsC) → ∃ δ, Sm B.toPre f δ B.KsC ∧ p B f δ T := by
  classical
  obtain ⟨a, b, c, d, h1, h2, h3⟩ := h
  refine ⟨fun B f F => if h : ∃ δ, Sm B f δ F then a B f h.choose F else ∅,
    fun B f F G => if h : ∃ δ, Sm B f δ F then b B f h.choose F G else ∅,
    fun B f F G l => if h : ∃ δ, Sm B f δ F then c B f h.choose F G l else ∅,
    fun B f F G X => if h : ∃ δ, Sm B f δ F then d B f h.choose F G X else ∅, ?_, ?_, ?_⟩
  · intro B f F z hz
    by_cases h : ∃ δ, Sm B f δ F
    · simp only [dif_pos h] at hz
      exact h1 _ _ _ _ z hz
    · simp [dif_neg h] at hz
  · intro B f F G X z hz
    by_cases h : ∃ δ, Sm B f δ F
    · simp only [dif_pos h] at hz
      exact h2 _ _ _ _ _ _ z hz
    · simp [dif_neg h] at hz
  · intro B f T hO hH hP hA h
    simp only [dif_pos h] at hH hP hA
    exact ⟨h.choose, h.choose_spec, h3 B f _ T hO h.choose_spec hH hP hA⟩

theorem ExTrueG.mono {KP : BaseP} {Q Q' : V4.Slot} (hE : ExTrueG KP Q) (h : ∀ K X f T c, Q K X f T c → Q' K X f T c) : ExTrueG KP Q' :=
  EvG.imp hE fun _ _ _ _ _ hK => hK.imp fun _ _ _ _ H hp =>
    let ⟨C, W, V, S, N, G, c, q⟩ := H hp
    ⟨C, W, V, S, N, G, c, h _ _ _ _ _ q⟩

theorem ExportG.anti {Q Q' : V4.Slot} (hE : ExportG Q) (h : ∀ K X f T c, Q' K X f T c → Q K X f T c) : ExportG Q' :=
  EvG.imp hE fun _ _ _ _ _ H X f T c q => H X f T c (h _ _ _ _ _ q)

theorem RetwistG.strengthen {Q Q₁ Q' : V4.Slot} (hR : RetwistG Q Q') (h : ∀ K X f T c, Q₁ K X f T c → Q K X f T c) :
    RetwistG Q₁ fun K X f T c => Q' K X f T c ∧ Q₁ K X f T c :=
  EvG.imp hR fun _ _ _ _ _ H X f T c q e A S₂ hS =>
    let ⟨B', f', T', a1, a2, a3, a4, a5, a6⟩ := H X f T c (h _ _ _ _ _ q) e A S₂ hS
    ⟨B', f', T', a1, a2, a3, a4, a5, fun C W V S N G c' q' =>
      (a6 C W V S N G c' (h _ _ _ _ _ q')).imp_right fun t => ⟨t, q'⟩⟩

theorem LargeBaseConditionG.passes {KP : BaseP} {Q Q' R : V4.Slot} (h : LargeBaseConditionG KP Q R) (h1 : ExTrueG KP Q) (h2 : ExportG Q) (h3 : RetwistG Q Q') :
    ExTrueG KP (fun K X f T c => Q K X f T c ∧ R K X f T c) ∧ ExportG (fun K X f T c => Q K X f T c ∧ R K X f T c) ∧
      RetwistG (fun K X f T c => Q K X f T c ∧ R K X f T c) fun K X f T c => Q' K X f T c ∧ R K X f T c := by
  refine ⟨(EvG.inter h h1).imp fun K _ _ _ _ H => (H.1.inter H.2).imp fun B f T _ t k => ?_, h2.anti fun _ _ _ _ _ q => q.1,
    EvG.imp (h3.strengthen (Q₁ := fun K X f T c => Q K X f T c ∧ R K X f T c) fun _ _ _ _ _ q => q.1) fun K _ _ _ _ H X f T c q e A S₂ a => ?_⟩
  · obtain ⟨C, W, V, S, N, G, c, q⟩ := t.2 k
    exact ⟨C, W, V, S, N, G, c, q, t.1 k C W V S N G c q⟩
  · obtain ⟨B', f', T', a1, a2, a3, a4, a5, a6⟩ := H X f T c q e A S₂ a
    exact ⟨B', f', T', a1, a2, a3, a4, a5, fun C W V S N G c' q' =>
      (a6 C W V S N G c' q').imp_right fun t => ⟨t.1, t.2.2⟩⟩

theorem baseCond_true (h2b : StandardLattice.SiegelMassRatioCM) : BaseCond fun _ _ => True := by
  refine ⟨(evG_of_ev (ev_preX_frame h2b)).imp fun K _ _ _ _ hfr => ?_, fun _ _ _ _ _ _ _ => trivial⟩
  obtain ⟨P, hP⟩ := Inh.exists_over K
  obtain ⟨f₀⟩ := (hfr _ hP).2
  refine ⟨P, f₀, hP, fun S₁ S₂ h₁ h₂ => ?_⟩
  obtain ⟨B₀, rfl, -⟩ := BaseExt.exists_base P ∅ ∅ ∅ (by simp) (by simp) (by simp)
  obtain ⟨B₁, e₁, k₁, l₁⟩ := Inh.exists_fixed B₀ (S₁ B₀.KsC) (h₁ _)
  obtain ⟨B, e, l₂⟩ := BaseEnl.exists_enl B₁ (S₂ B₀.KsC B₁.fixedCoefficientFieldInComplex) (h₂ _ _)
  have hk : B.KsC = B₀.KsC := e.KsC_eq.trans k₁
  have e' : B.toPre = B₀.toPre := e.1.trans e₁
  refine ⟨B, e' ▸ f₀, e', by simp, trivial, ?_⟩
  rw [hk, Has₂, e.fixedCoefficientField_eq]
  exact ⟨l₁, l₂⟩

section Tests
variable (hH : DC.HostExQ) (hLP : LevelPrime) (h2b : StandardLattice.SiegelMassRatioCM)
include hH hLP h2b

theorem not_baseCond_false : ¬ BaseCond fun _ _ => False := fun h =>
  Inh.not_evG_false hH hLP h2b (h.ex.imp fun _ _ _ _ _ ⟨_, _, _, H⟩ =>
    let ⟨_, _, _, _, t, _⟩ := H (fun _ => ∅) (fun _ _ => ∅) (by simp) (by simp); t)

theorem not_exTrueG_false {KP : BaseP} (hK : BaseCond KP) : ¬ ExTrueG KP fun _ _ _ _ _ => False := fun hE => by
  refine Inh.not_evG_false hH hLP h2b ((hK.ex.inter hE).imp ?_)
  rintro K _ _ _ _ ⟨⟨P, f₀, hP, hks⟩, S₁, P₁, A, S₂, a₁, a₂, hlg⟩
  obtain ⟨B, f, hB, hf, hKP, hH₁, hH₂⟩ := hks (S₁ P f₀) (fun F F₀ => S₂ P f₀ F F₀ {1, f₀.del, f₀.del'}) (a₁ _ _)
    (fun F F₀ => a₂ _ _ F F₀ _)
  subst hB
  obtain rfl := eq_of_heq hf
  have hs : (TwDat.untw B (P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex)).set f = {1, f.del, f.del'} := by
    refine Set.union_eq_left.2 ?_
    rintro _ ⟨w, rfl⟩
    change (if _ then f.del' else f.del) * 1 ∈ _
    rw [mul_one]
    split_ifs
    · exact .inr (.inr rfl)
    · exact .inr (.inl rfl)
  obtain ⟨_, _, _, _, _, _, _, h⟩ := hlg B f (TwDat.untw B (P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex)) hP
    ⟨hH₁, by rw [hs]; exact hH₂⟩ (Finset.Subset.refl _) (fun w v hv => absurd hv (Finset.notMem_empty _)) hKP
  exact h

theorem not_firstG_false {KP : BaseP} (hK : BaseCond KP) : ¬ FirstG KP fun _ _ _ _ _ => False := fun hE => by
  refine Inh.not_evG_false hH hLP h2b ((hK.ex.inter (EvG.imp hE fun K _ _ _ _ H => (H.inter (lg_forced K)).imp fun _ _ _ _ G a b => G.1 a G.2 b)).imp ?_)
  rintro K _ _ _ _ ⟨⟨P, f₀, hP, hks⟩, S₁, P₁, A, S₂, a₁, a₂, hlg⟩
  obtain ⟨B, f, hB, hf, hKP, hH₁, hH₂⟩ := hks (S₁ P f₀) (fun F F₀ => S₂ P f₀ F F₀ {1, f₀.del, f₀.del'}) (a₁ _ _)
    (fun F F₀ => a₂ _ _ F F₀ _)
  subst hB
  obtain rfl := eq_of_heq hf
  have hs : (TwDat.untw B (P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex)).set f = {1, f.del, f.del'} := by
    refine Set.union_eq_left.2 ?_
    rintro _ ⟨w, rfl⟩
    change (if _ then f.del' else f.del) * 1 ∈ _
    rw [mul_one]
    split_ifs
    · exact .inr (.inr rfl)
    · exact .inr (.inl rfl)
  obtain ⟨_, _, _, _, _, _, _, h⟩ := hlg B f (TwDat.untw B (P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex)) hP
    ⟨hH₁, by rw [hs]; exact hH₂⟩ (Finset.Subset.refl _) (fun w v hv => absurd hv (Finset.notMem_empty _)) hKP rfl
  exact h

end Tests

end GlobalTheory.Mem.Top.GroupRetwisting

end
