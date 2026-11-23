import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse

noncomputable section

namespace GlobalTheory.Fc.LgModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField

variable {KP : ∀ B : Base, Fr B.toPre → Prop} {Q Q' R : V4.Slot} {Bd : BdT} {Lk : LkT Bd}

theorem ev_all {p : Ctx → Prop} (h : ∀ K, p K) : Ev p :=
  ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨0,
    fun K _ _ _ _ _ => h K⟩⟩⟩⟩⟩

theorem largeBaseProperty_of_eventually {p : Ctx → ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : EvLg p) :
    LargeBaseCondition KP Q fun K X f T _ => p K X.B f T :=
  eventuallyAllScaleContexts_mono_of_imp (fun _ H => H.imp fun _ _ _ _ t _ _ _ _ _ _ _ _ _ => t) h

theorem largeBaseProperty_of_isAlgebraic (S₁ S₂ : Ctx → Finset ℂ) (P : Ctx → Finset ℕ) (A : Ctx → ℕ → Finset ℕ)
    (h₁ : ∀ K, ∀ z ∈ S₁ K, IsAlgebraic ℚ z) (h₂ : ∀ K, ∀ z ∈ S₂ K, IsAlgebraic ℚ z) :
    LargeBaseCondition KP Q fun K X _ T _ => Has₂ X.B (S₁ K) (S₂ K) ∧ P K ⊆ T.pl ∧ T.Avoids (A K) :=
  largeBaseProperty_of_eventually (p := fun K B _ T => Has₂ B (S₁ K) (S₂ K) ∧ P K ⊆ T.pl ∧ T.Avoids (A K))
    (ev_all fun K => ⟨fun _ _ _ => S₁ K, fun _ _ _ _ => P K, fun _ _ _ _ => A K, fun _ _ _ _ _ => S₂ K,
      fun _ _ _ => h₁ K, fun _ _ _ _ _ => h₂ K, fun _ _ _ _ a b c => ⟨a, b, c⟩⟩)

theorem largeBaseProperty_self : LargeBaseCondition KP Q fun K X f T c => KP X.B f ∧ Q K X f T c :=
  ev_all fun K => GroupRetwisting.lg_all K fun _ _ _ _ k _ _ _ _ _ _ _ q => ⟨k, q⟩

theorem largeBaseProperty_mono {R' : V4.Slot} (h : LargeBaseCondition KP Q R) (hR : ∀ K X f T c, R K X f T c → R' K X f T c) : LargeBaseCondition KP Q R' :=
  eventuallyAllScaleContexts_mono_of_imp (fun _ H => H.imp fun _ _ _ _ t k C W V S N G c q => hR _ _ _ _ _ (t k C W V S N G c q)) h

theorem exBL_of_exB (h : ExB Q' Lk) : ExBL KP Q Q' Lk :=
  ⟨_, largeBaseProperty_true, EvP.mono (fun _ _ _ H β q => H β q.1) h⟩

theorem not_rowL_false : ¬ RowL KP Q Q' Lk fun _ _ => False := fun ⟨_, _, _, _, h⟩ =>
  h (fun _ => False) (fun _ hc => hc.elim) fun _ hc => hc.elim

theorem not_largeBaseProperty_of_disjoint (hH : DC.HostExQ) (hLP : LevelPrime) (h2b : StandardLattice.SiegelMassRatioCM)
    (hK : GroupRetwisting.BaseCond KP) (hE : V4.ExTrue KP Q) (hd : ∀ K X f T c, Q K X f T c → ¬ R K X f T c) : ¬ LargeBaseCondition KP Q R := fun h => by
  refine GroupRetwisting.not_exTrueG_false hH hLP h2b hK (GroupRetwisting.exTrueG_of (eventuallyAllScaleContexts_mono_of_imp ?_ (eventuallyAllScaleContexts_and_of_both h hE)))
  intro K H
  refine (H.1.inter H.2).imp ?_
  intro B f T _ t k
  obtain ⟨C, W, V, S, N, G, c, q⟩ := t.2 k
  exact ⟨C, W, V, S, N, G, c, hd _ _ _ _ _ q (t.1 k C W V S N G c q)⟩

theorem congr_frame {α : Type*} (g : ∀ P : Pre, Fr P → α) {P P' : Pre} {f : Fr P} {f' : Fr P'} (h : P = P') (hf : HEq f f') :
    g P f = g P' f' := by
  subst h
  rw [eq_of_heq hf]

theorem cores_of_passes (hK : GroupRetwisting.BaseCond KP) (h1 : V4.ExTrue KP Q) (h2 : V4.Export Q) (h3 : V4.Retwist Q Q') :
    EvG fun K => ∃ X f T c, Q' K X f T c := by
  refine (hK.ex.inter (evG_of_ev (eventuallyAllScaleContexts_and_of_both h1 (eventuallyAllScaleContexts_and_of_both h2 h3)))).imp ?_
  rintro K _ _ _ _ ⟨⟨P, f₀, hP₀, hks⟩, ⟨S₁, P₁, A, S₂, a₁, a₂, hlg⟩, hex, hre⟩
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
  obtain ⟨C, W, V, S, N, G, c, hQ⟩ := hlg B f (TwDat.untw B (P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex)) hP₀
    ⟨hH₁, by rw [hs]; exact hH₂⟩ (Finset.Subset.refl _) (fun w v hv => absurd hv (Finset.notMem_empty _)) hKP
  obtain ⟨B', f', T', hEnl, hf', hpl, hAv, hS, hfin⟩ := hre ⟨B, C, W, V, S, N, G⟩ f _ c hQ (hex ⟨B, C, W, V, S, N, G⟩ f _ c hQ)
    (A B.toPre f B.KsC B.fixedCoefficientFieldInComplex) (fun P g Ξ => S₂ P g B.KsC B.fixedCoefficientFieldInComplex Ξ) (fun P g Ξ => a₂ P g _ _ Ξ)
  have hP : B'.toPre = B.toPre := hEnl.1
  have hk : B'.KsC = B.KsC := hEnl.KsC_eq
  have hl : B'.fixedCoefficientFieldInComplex = B.fixedCoefficientFieldInComplex := hEnl.fixedCoefficientField_eq
  have hO' : K.Over B'.toPre := hP ▸ hP₀
  obtain ⟨C', W', V', S', N', G', c', hQ'⟩ := hlg B' f' T' hO'
    ⟨by rw [hk, hl, congr_frame S₁ hP hf']; exact hH₁, by rw [hk, hl]; exact hS⟩
    (by rw [hk, hl, congr_frame P₁ hP hf', hpl]; exact Finset.Subset.refl _)
    (by rw [hk, hl, congr_frame A hP hf']; exact hAv) (hK.enl B B' f f' hEnl hf' hKP)
  exact ⟨⟨B', C', W', V', S', N', G'⟩, f', T', c', (hfin C' W' V' S' N' G' c' hQ').2⟩

theorem cores_sAnd (hK : GroupRetwisting.BaseCond KP) (h1 : V4.ExTrue KP Q) (h2 : V4.Export Q) (h3 : V4.Retwist Q Q') (h : LargeBaseCondition KP Q R) :
    EvG fun K => ∃ X f T c, sAnd Q' R K X f T c :=
  let p := h.passes h1 h2 h3
  cores_of_passes hK p.1 p.2.1 p.2.2

theorem not_void (hH : DC.HostExQ) (hLP : LevelPrime) (h2b : StandardLattice.SiegelMassRatioCM) (hK : GroupRetwisting.BaseCond KP)
    (h1 : V4.ExTrue KP Q) (h2 : V4.Export Q) (h3 : V4.Retwist Q Q') (h : LargeBaseCondition KP Q R) :
    ∃ K X f T c, Q' K X f T c ∧ R K X f T c := by
  by_contra hn
  refine Inh.not_evG_false hH hLP h2b ((cores_sAnd hK h1 h2 h3 h).imp ?_)
  rintro K _ _ _ _ ⟨X, f, T, c, q⟩
  exact hn ⟨K, X, f, T, c, q⟩

theorem baseCond_of_ksCond (h2b : StandardLattice.SiegelMassRatioCM) (hK : V4.KsCond KP) : GroupRetwisting.BaseCond KP := by
  have h := GroupRetwisting.baseCond_of (PP := fun _ _ => True) hK ((GroupRetwisting.baseCond_true h2b).ex.imp fun _ _ _ _ _ ⟨P, f, a, _⟩ => ⟨P, f, a, trivial⟩)
  simpa using h

theorem exBL_of_false : ExBL (fun _ _ => False) Q Q' Lk :=
  ⟨fun _ _ _ _ _ => False, ev_all fun K => GroupRetwisting.lg_all K fun _ _ _ _ k => k.elim, EvP.of_all fun _ _ _ _ q => q.2.elim⟩

theorem exBL_of_disjoint (hd : ∀ K X f T c, Q' K X f T c → ¬ Q K X f T c) : ExBL KP Q Q' Lk :=
  ⟨_, largeBaseProperty_self, EvP.of_all fun _ _ _ _ q => (hd _ _ _ _ _ q.1 q.2.2).elim⟩

def LgAt (KP : ∀ B : Base, Fr B.toPre → Prop) (Q R : V4.Slot) (K : Ctx) : Prop :=
  large₂ K fun B f T => KP B f → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c → R K ⟨B, C, W, V, S, N, G⟩ f T c

theorem largeBaseProperty_conditional : LargeBaseCondition KP Q fun K X f T c => LgAt KP Q R K → R K X f T c :=
  ev_all fun K => by
    by_cases h : LgAt KP Q R K
    · exact large₂.imp h fun _ _ _ _ t k C W V S N G c q _ => t k C W V S N G c q
    · exact GroupRetwisting.lg_all K fun _ _ _ _ _ _ _ _ _ _ _ _ _ a => (h a).elim

theorem exBL_of_good (h : GroupRetwisting.LargeBaseConditionG KP Q R) (hx : ExB (sAnd Q' R) Lk) : ExBL KP Q Q' Lk :=
  ⟨_, largeBaseProperty_conditional (R := R), ((EvP.of_evGd h).and hx).mono fun _ _ _ H β q => H.2 β ⟨q.1, q.2 H.1⟩⟩

theorem rowL_of_good {H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (h : GroupRetwisting.LargeBaseConditionG KP Q R) (hr : Row (sAnd Q' R) Lk H) :
    RowL KP Q Q' Lk H := by
  obtain ⟨E, e, hH⟩ := hr
  refine ⟨_, largeBaseProperty_conditional (R := R), fun κ D O c b => Built (sAnd Q' R) Lk κ D O c b ∧ E κ D O c b,
    ((EvP.of_evGd h).and e).mono fun _ _ hk t β q c b l =>
      ⟨Built.intro hk ⟨q.1, q.2 t.1⟩ l, t.2 β ⟨q.1, q.2 t.1⟩ c b l⟩, fun 𝒜 σ s => hH 𝒜 σ fun Fm hc => ?_⟩
  obtain ⟨κ, a, b, t⟩ := s Fm hc
  exact ⟨κ, a, b, fun x hx i => (t x hx i).2⟩

end GlobalTheory.Fc.LgModel

end
