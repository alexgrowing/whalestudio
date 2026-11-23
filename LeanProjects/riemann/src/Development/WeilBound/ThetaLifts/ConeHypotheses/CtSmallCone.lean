import Development.WeilBound.ThetaLifts.ConeHypotheses.KeyAOf

noncomputable section

namespace PositivityTheory.ThKG

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

structure Leaves : Prop where
  evZero : EvZero
  evCone : EvCone
  stabEx : StabEx
  towerA : TowerA
  towerB : TowerB
  facNe : FacNe
  matchEx : MatchEx
  leviEx : LeviEx
  polDense : PolDense
  weilConv : WeilConv
  soCont : SoCont
  splitEx : SplitEx
  ctBigZero : CTBigZero
  ctSmallZero : CTSmallZero
  ctBigCone : CTBigCone
  ctSmallCone : CTSmallCone
  anAll : AnAll
  polRe : PolRe
  nonZeroAn : NonZeroAn
  polZero : PolZero
  locA : LocA'
  locB : LocB'
  endA : EndA'
  endB : EndB'
  kReal : KReal
  kFin : KFin

namespace Leaves

variable (L : Leaves)
include L

theorem keyB : ∃ e₁ e₂ s, KeyB e₁ e₂ s := keyB_of L.evZero L.evCone L.stabEx L.ctBigZero L.ctSmallCone L.locB L.leviEx

theorem keyA : ∃ e₁ e₂ s, KeyA e₁ e₂ s :=
  keyA_of L.evZero L.evCone L.stabEx L.ctSmallZero L.ctBigCone L.locA L.leviEx L.anAll L.matchEx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
  {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem matched (t : IsTriple B G X om om') : ∃ R Rf, IsMatched B G X om om' R Rf :=
  matching_of_parts L.kReal L.kFin F E σ B a a' G X om om' t

theorem conv (t : IsTriple B G X om om') : ∀ Φ ∈ schA F _, G.M.Conv om Φ := fun Φ h =>
  ((L.weilConv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) (weilCondV t)).1 Φ h).1

theorem nz_move (t : IsTriple B G X om om') {V V' W} (t₂ : IsTriple B (reG G V V' W) X om om')
    (h : ∃ Φ ∈ PolData B (reG G V V' W).M, G.M.I om Φ ≠ 0) : ∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨Φ, hΦ, hne⟩ := h
  refine hne ?_
  clear hne
  have key : Φ ∈ schA F _ ∧ G.M.I om Φ = 0 := by
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, -, φ, h1, h2, rfl⟩ := h
      obtain ⟨g, hg, e⟩ := pure_eq_pureA t.geo.hM φ h1 h2
      refine ⟨e f ▸ pureA_mem f hg, funext fun x => ?_⟩
      have hc := (L.weilConv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) (weilCondV t)).2 g hg x
      have := Continuous.ext_on (L.polDense F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t)) hc continuous_const (g := fun _ => (0 : ℂ))
        fun f₁ hf₁ => by
          have := hn _ (Submodule.subset_span ⟨f₁, hf₁, φ, h1, h2, rfl⟩)
          rw [e f₁] at this
          exact congrFun this x
      rw [e f]
      exact congrFun this f
    | zero => exact ⟨Submodule.zero_mem _, I_zero _ _⟩
    | add Φ Ψ _ _ h1 h2 =>
      exact ⟨Submodule.add_mem _ h1.1 h2.1, funext fun x => by rw [I_add t.weil (L.conv t) h1.1 h2.1, h1.2, h2.2]; simp⟩
    | smul c Φ _ h1 => exact ⟨Submodule.smul_mem _ _ h1.1, funext fun x => by rw [I_smul, h1.2]; simp⟩
  exact key.2

variable {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem const_of (m : IsMatched B G X om om' R Rf) (hB : Below (G.p + G.q)) : ∃ c, c ≠ 0 ∧ PolConst B G X om om' R Rf c := by
  have t := m.triple
  have hb := t.geo.eBig
  rcases Nat.eq_zero_or_pos G.q with hq | hq
  · rcases Nat.eq_zero_or_pos G.p with hp | hp
    · exact L.polZero F E σ B a a' G X om om' R Rf m hp hq
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
    obtain ⟨V, V', W, t₂, G₁, H, H', cfg, om₁, om₁', t₁⟩ := L.towerA F E σ B b a' G X om om' t hq hp
    obtain ⟨R₂, Rf₂, m₂⟩ := L.matched t₂
    obtain ⟨R₁, Rf₁, m₁⟩ := L.matched t₁
    refine L.polRe F E σ B _ _ G X om om' R Rf m V V' W R₂ Rf₂ m₂ ?_
    obtain ⟨e₁, e₂, s, key⟩ := L.keyA
    obtain ⟨C, hC, key⟩ := key F E σ B b a' _ G₁ H H' cfg R₂ R₁
    have hlt : G₁.p + G₁.q < G.p + G.q := by
      have h1 : G₁.p + 1 = G.p := cfg.ep
      have := cfg.q1
      omega
    obtain ⟨⟨c₁, hc₁, pc₁⟩, -⟩ := hB F E σ B _ _ G₁ X om₁ om₁' R₁ Rf₁ m₁ hlt
    obtain ⟨f1, f2⟩ := L.facNe F E σ B _ _ G X om om' t e₁ e₂ s H.𝔟 H'.𝔟 (1 - (((b + 2 - a') / 2 : ℕ) : ℤ))
    refine ⟨_, mul_ne_zero (mul_ne_zero (mul_ne_zero hC f1) (f2 ((b + 2 - a') / 2) (by omega))) hc₁,
      L.endA F E σ B _ _ (reG G V V' W) X om om' R₂ Rf₂ m₂ hq hp hB _ G₁.W H' _ _ cfg.hH' _ ?_⟩
    intro Φ Φ' so pm fa fb fa' fb' sp sp' h₁ l hl
    obtain ⟨fa'', sp'', rel⟩ := (key X om om' Rf₂ om₁ om₁' Rf₁ m₂ m₁ hB c₁ pc₁ _ rfl).1 Φ Φ' pm
    have u := ((L.splitEx F E σ B _ _ (reG G V V' W) X om om' t₂ _ G₁.W H' _ _ cfg.hH').2 Φ' ⟨(polMatch_mem pm).2, so⟩).unique
      (y₁ := (fa', fb')) (y₂ := (fa'', 0)) sp' sp''
    obtain rfl : fa' = fa'' := congrArg Prod.fst u
    exact rel fa fb sp h₁ l hl
  · have ha := t.geo.aBig
    obtain ⟨b, rfl⟩ : ∃ b, a' = b + 2 := ⟨a' - 2, by omega⟩
    obtain ⟨V, V', W, t₂, G₁, H, H', cfg, om₁, om₁', t₁⟩ := L.towerB F E σ B a b G X om om' t hq
    obtain ⟨R₂, Rf₂, m₂⟩ := L.matched t₂
    obtain ⟨R₁, Rf₁, m₁⟩ := L.matched t₁
    refine L.polRe F E σ B _ _ G X om om' R Rf m V V' W R₂ Rf₂ m₂ ?_
    obtain ⟨e₁, e₂, s, key⟩ := L.keyB
    obtain ⟨C, hC, key⟩ := key F E σ B a b _ G₁ H H' cfg R₂ R₁
    have hlt : G₁.p + G₁.q < G.p + G.q := by
      have h1 : G₁.p = G.p := cfg.ep
      have h2 : G₁.q + 1 = G.q := cfg.eq
      omega
    obtain ⟨⟨c₁, hc₁, pc₁⟩, -⟩ := hB F E σ B _ _ G₁ X om₁ om₁' R₁ Rf₁ m₁ hlt
    obtain ⟨f1, f2⟩ := L.facNe F E σ B _ _ G X om om' t e₁ e₂ s H.𝔟 H'.𝔟 (-(((a - (b + 2)) / 2 : ℕ) : ℤ))
    have f3 := f2 ((a - (b + 2)) / 2 + 1) (by omega)
    rw [Nat.cast_add, Nat.cast_one] at f3
    have hk := mul_ne_zero (mul_ne_zero hC f1) f3
    refine ⟨_, div_ne_zero hc₁ hk, L.endB F E σ B _ _ (reG G V V' W) X om om' R₂ Rf₂ m₂ hq hB _ G₁.W H' _ _ cfg.hH' _ ?_⟩
    intro Φ Φ' so pm fa fb fa' fb' sp sp' h₁ l hl
    have := (key X om om' Rf₂ om₁ om₁' Rf₁ m₂ m₁ hB).1 c₁ pc₁ Φ Φ' so pm fa fb fa' fb' sp sp' h₁ l hl
    rw [div_mul_eq_mul_div, eq_div_iff hk, mul_comm]
    exact this

theorem nzV (t : IsTriple B G X om om') (hq : 1 ≤ G.q) (hB : Below (G.p + G.q)) : ∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0 := by
  have ha := t.geo.aBig
  obtain ⟨b, rfl⟩ : ∃ b, a' = b + 2 := ⟨a' - 2, by omega⟩
  obtain ⟨V, V', W, t₂, G₁, H, H', cfg, om₁, om₁', t₁⟩ := L.towerB F E σ B a b G X om om' t hq
  obtain ⟨R₂, Rf₂, m₂⟩ := L.matched t₂
  obtain ⟨R₁, Rf₁, m₁⟩ := L.matched t₁
  obtain ⟨e₁, e₂, s, key⟩ := L.keyB
  obtain ⟨C, -, key⟩ := key F E σ B a b _ G₁ H H' cfg R₂ R₁
  obtain ⟨Φ, hΦ, h⟩ := (key X om om' Rf₂ om₁ om₁' Rf₁ m₂ m₁ hB).2
  refine L.nz_move t t₂ ⟨Φ, hΦ, fun z => ?_⟩
  obtain ⟨_, _, _, hne⟩ := h 0 0 (by
    show Split2 _ _ _ (G.M.I om Φ) 0 0
    rw [z]
    exact ⟨fun _ _ _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩)
  exact hne rfl

theorem claim_of (m : IsMatched B G X om om' R Rf) (hB : Below (G.p + G.q)) : Claim B G X om om' R Rf := by
  obtain ⟨c, hc, pc⟩ := L.const_of m hB
  obtain ⟨m1, m2, -⟩ := L.matchEx F E σ B _ _ G X om om' R Rf m
  refine ⟨⟨c, hc, pc⟩, ?_⟩
  rcases Nat.eq_zero_or_pos G.q with hq | hq
  · obtain ⟨Φ', ⟨h1, h2⟩, hne⟩ := (L.nonZeroAn F E σ B _ _ G X om om' m.triple).2 hq
    obtain ⟨Φ, pm⟩ := m2 Φ' h1
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
    exact ⟨⟨Φ, (polMatch_mem pm).1, Function.ne_iff.2 ⟨x, by rw [pc Φ Φ' h2 pm x]; exact mul_ne_zero hc hx⟩⟩, Φ', ⟨h1, h2⟩, hne⟩
  · obtain ⟨Φ, h1, hne⟩ := L.nzV m.triple hq hB
    obtain ⟨Φ', so, pm⟩ := m1 Φ h1
    refine ⟨⟨Φ, h1, hne⟩, Φ', ⟨(polMatch_mem pm).2, so⟩, fun z => hne (funext fun x => ?_)⟩
    rw [pc Φ Φ' so pm x, z]
    simp

theorem below (n : ℕ) : Below n := by
  induction n with
  | zero => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)
  | succ n ih => exact fun F E _ _ _ _ _ σ B a a' G X om om' R Rf m h => L.claim_of m (ih.mono (by omega))

theorem claim (m : IsMatched B G X om om' R Rf) : Claim B G X om om' R Rf := L.claim_of m (L.below _)

theorem polConst_of (m : IsMatched B G X om om' R Rf) {c : ℂ} (h : IsConst B G X om om' R Rf c) : PolConst B G X om om' R Rf c :=
  fun Φ Φ' so pm => h Φ Φ' ((L.matchEx F E σ B _ _ G X om om' R Rf m).2.2 Φ Φ' so pm).2.2

theorem isConst_of (m : IsMatched B G X om om' R Rf) {c : ℂ} (h : PolConst B G X om om' R Rf c) : IsConst B G X om om' R Rf c := by
  rintro Φ Φ' ⟨so, k, k', g, f, s, g', f', s', h1, h2, rfl, rfl, h3⟩ x
  have t := m.triple
  have l2 := L.soCont F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t) k' g' f' s' h2 (fun j => (h3 j).1) so x
  have e : ∀ u : Fin k → SInf F _, G.M.I om (∑ i, pureA F (u i) (g i)) x = ∑ i, G.M.I om (pureA F (u i) (g i)) x := fun u =>
    I_sum t.weil (L.conv t) _ _ (fun i => pureA_mem _ (h1 i).1) x
  have l1 : Tendsto (fun j => G.M.I om (∑ i, pureA F (s j i) (g i)) x) atTop (𝓝 (G.M.I om (∑ i, pureA F (f i) (g i)) x)) := by
    simp only [e]
    exact tendsto_finset_sum _ fun i _ =>
      (((L.weilConv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) (weilCondV t)).2 _ (h1 i).1 x).tendsto _).comp (h1 i).2
  exact tendsto_nhds_unique l1 ((l2.const_mul c).congr fun j => (h _ _ (h3 j).1 (h3 j).2 x).symm)

theorem kConst : KConst := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf m
  obtain ⟨⟨c, hc, pc⟩, -, Φ', ⟨h1, so⟩, hne⟩ := L.claim m
  obtain ⟨Φ, pm⟩ := (L.matchEx F E σ B _ _ G X om om' R Rf m).2.1 Φ' h1
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
  have u : ∀ c', IsConst B G X om om' R Rf c' → c' = c := fun c' h =>
    mul_right_cancel₀ hx ((L.polConst_of m h Φ Φ' so pm x).symm.trans (pc Φ Φ' so pm x))
  exact ⟨⟨Φ', so, hne⟩, ⟨c, L.isConst_of m pc, u⟩, fun c' h => u c' h ▸ hc⟩

theorem kBeta : KBeta := by
  obtain ⟨e₁, e₂, s, key⟩ := L.keyB
  refine ⟨e₁, e₂, s, fun F E _ _ _ _ _ σ B a b G G₁ H H' R R₁ h1 h2 h3 h4 h5 => ?_⟩
  obtain ⟨C, hC, key⟩ := key F E σ B a b G G₁ H H' ⟨h1, h2, h3, h4, h5⟩ R R₁
  refine ⟨C, hC, fun X om om' Rf om₁ om₁' Rf₁ m m₁ c c₁ hc hc₁ => ?_⟩
  obtain ⟨k1, Φ, hΦ, k2⟩ := key X om om' Rf om₁ om₁' Rf₁ m m₁ (L.below _)
  obtain ⟨Φ', so, pm⟩ := (L.matchEx F E σ B _ _ G X om om' R Rf m).1 Φ hΦ
  obtain ⟨⟨fa', fb'⟩, sp', -⟩ := (L.splitEx F E σ B _ _ G X om om' m.triple _ G₁.W H' _ _ h5).2 Φ' ⟨(polMatch_mem pm).2, so⟩
  have e : G.M.I om Φ = c • G.M'.I om' Φ' := funext (L.polConst_of m hc Φ Φ' so pm)
  have sp : Split2 G₁.W H' X (G.M.I om Φ) (c • fa') (c • fb') := e ▸ split2_smul sp' c
  obtain ⟨h₁, l, hl, hne⟩ := k2 _ _ sp
  have := k1 c₁ (L.polConst_of m₁ hc₁) Φ Φ' so pm _ _ _ _ sp sp' h₁ l hl
  have f1 := (L.facNe F E σ B _ _ G X om om' m.triple e₁ e₂ s H.𝔟 H'.𝔟 (-(((a - (b + 2)) / 2 : ℕ) : ℤ))).1
  have hk := mul_ne_zero hC f1
  simp only [Pi.smul_apply, smul_eq_mul] at this hne
  refine ⟨_, inv_mul_cancel₀ hk, ?_⟩
  rw [eq_inv_mul_iff_mul_eq₀ hk]
  refine mul_right_cancel₀ (right_ne_zero_of_mul hne) ?_
  linear_combination this

theorem kAlpha : KAlpha := by
  obtain ⟨e₁, e₂, s, key⟩ := L.keyA
  refine ⟨e₁, e₂, s, fun F E _ _ _ _ _ σ B b a' G G₁ H H' R R₁ h1 h2 h3 h4 h5 h6 => ?_⟩
  obtain ⟨C, hC, key⟩ := key F E σ B b a' G G₁ H H' ⟨h1, h2, h3, h4, h5, h6⟩ R R₁
  refine ⟨C, hC, fun X om om' Rf om₁ om₁' Rf₁ m m₁ c c₁ hc hc₁ => ?_⟩
  obtain ⟨-, Φ, Φ', fa', pm, ⟨sp', rel⟩, h₁, l, hl, hne⟩ :=
    key X om om' Rf om₁ om₁' Rf₁ m m₁ (L.below _) c₁ (L.polConst_of m₁ hc₁) _ rfl
  have e : G.M.I om Φ = c • G.M'.I om' Φ' :=
    funext (L.anAll F E σ B _ _ G X om om' R Rf m h2 c (L.polConst_of m hc) Φ Φ' pm)
  have := rel _ _ (e ▸ split2_smul sp' c) h₁ l hl
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hne this

end Leaves

end PositivityTheory.ThKG

end
