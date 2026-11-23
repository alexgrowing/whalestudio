import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.RowTieFB

noncomputable section

open Filter Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.ActLimit

variable {C : Type} [Field C] {V : VF C}

def Tends (V : VF C) (s : ℕ → C) (x : C) : Prop := ∀ w : ℝ, ∀ᶠ n in atTop, V.Ge w (x - s n)

theorem exists_ge (x : C) : ∃ w : ℝ, w ≤ 0 ∧ V.Ge w x := by
  unfold VF.Ge
  induction V.v x using WithTop.recTopCoe with
  | top => exact ⟨0, le_rfl, le_top⟩
  | coe t => exact ⟨min t 0, min_le_right _ _, by exact_mod_cast min_le_left _ _⟩

theorem eq_zero_of_ge {x : C} (h : ∀ w : ℝ, V.Ge w x) : x = 0 := by
  by_contra hx
  have hv : V.v x ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hv
  have h1 := h (t + 1)
  unfold VF.Ge at h1
  rw [← ht] at h1
  have : t + 1 ≤ t := by exact_mod_cast h1
  linarith

theorem Tends.const (x : C) : Tends V (fun _ => x) x := fun w =>
  Eventually.of_forall fun _ => by simpa using VF.Ge.zero (V := V) w

theorem Tends.add {s t : ℕ → C} {x y : C} (hs : Tends V s x) (ht : Tends V t y) :
    Tends V (fun n => s n + t n) (x + y) := fun w => by
  filter_upwards [hs w, ht w] with n h1 h2
  have := h1.add h2
  rwa [show x - s n + (y - t n) = x + y - (s n + t n) by ring] at this

theorem Tends.neg {s : ℕ → C} {x : C} (hs : Tends V s x) : Tends V (fun n => -s n) (-x) := fun w => by
  filter_upwards [hs w] with n h1
  have := h1.neg
  rwa [show -(x - s n) = -x - -s n by ring] at this

theorem Tends.mul {s t : ℕ → C} {x y : C} (hs : Tends V s x) (ht : Tends V t y) :
    Tends V (fun n => s n * t n) (x * y) := fun w => by
  obtain ⟨a, -, ha⟩ := exists_ge (V := V) x
  obtain ⟨b, -, hb⟩ := exists_ge (V := V) y
  filter_upwards [hs (w - b), ht (w - a), ht b] with n h1 h2 h3
  have h4 : V.Ge b (t n) := by simpa using hb.sub h3
  have h5 : V.Ge w (x * (y - t n)) := by simpa using ha.mul h2
  have h6 : V.Ge w ((x - s n) * t n) := by simpa using h1.mul h4
  have := h5.add h6
  rwa [show x * (y - t n) + (x - s n) * t n = x * y - s n * t n by ring] at this

theorem Tends.unique {s : ℕ → C} {x y : C} (hx : Tends V s x) (hy : Tends V s y) : x = y := by
  apply sub_eq_zero.1
  refine eq_zero_of_ge (V := V) fun w => ?_
  obtain ⟨n, h1, h2⟩ := ((hx w).and (hy w)).exists
  simpa using h1.sub h2

theorem Tends.ge {s : ℕ → C} {x : C} {w : ℝ} (hx : Tends V s x) (hs : ∀ n, V.Ge w (s n)) : V.Ge w x := by
  obtain ⟨n, h1⟩ := (hx w).exists
  simpa using h1.add (hs n)

def convRing (V : VF C) : Subring ((ℕ → C) × C) where
  carrier := {p | Tends V p.1 p.2}
  mul_mem' := fun ha hb => Tends.mul ha hb
  one_mem' := Tends.const 1
  add_mem' := fun ha hb => Tends.add ha hb
  zero_mem' := Tends.const 0
  neg_mem' := fun ha => Tends.neg ha

def TendsS (V : VF C) {τ : Type} (f : ℕ → MvPowerSeries τ C) (g : MvPowerSeries τ C) : Prop :=
  ∀ μ, Tends V (fun n => MvPowerSeries.coeff μ (f n)) (MvPowerSeries.coeff μ g)

theorem TendsS.const {τ : Type} (g : MvPowerSeries τ C) : TendsS V (fun _ => g) g := fun _ => Tends.const _

theorem TendsS.sub {τ : Type} {f f' : ℕ → MvPowerSeries τ C} {g g' : MvPowerSeries τ C}
    (h : TendsS V f g) (h' : TendsS V f' g') : TendsS V (fun n => f n - f' n) (g - g') := fun μ => by
  simpa [sub_eq_add_neg] using (h μ).add (h' μ).neg

theorem TendsS.unique {τ : Type} {f : ℕ → MvPowerSeries τ C} {g g' : MvPowerSeries τ C}
    (h : TendsS V f g) (h' : TendsS V f g') : g = g' := by
  ext μ; exact (h μ).unique (h' μ)

theorem TendsS.const_zero {τ : Type} {f : ℕ → MvPowerSeries τ C} {g : MvPowerSeries τ C}
    (h : TendsS V f g) (hf : ∀ n, MvPowerSeries.constantCoeff (f n) = 0) : MvPowerSeries.constantCoeff g = 0 := by
  have h0 := h 0
  simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf] at h0
  exact h0.unique (Tends.const 0)

def TendsS.lift {τ : Type} {f : ℕ → MvPowerSeries τ C} {g : MvPowerSeries τ C} (h : TendsS V f g) :
    MvPowerSeries τ (convRing V) :=
  fun μ => ⟨(fun n => MvPowerSeries.coeff μ (f n), MvPowerSeries.coeff μ g), h μ⟩

def term (V : VF C) (n : ℕ) : convRing V →+* C :=
  ((Pi.evalRingHom (fun _ : ℕ => C) n).comp (RingHom.fst _ _)).comp (convRing V).subtype

def lim (V : VF C) : convRing V →+* C := (RingHom.snd _ _).comp (convRing V).subtype

theorem TendsS.subst {σ τ : Type} [Finite σ] {a : ℕ → σ → MvPowerSeries τ C} {b : σ → MvPowerSeries τ C}
    (ha : ∀ n s, MvPowerSeries.constantCoeff (a n s) = 0) (hab : ∀ s, TendsS V (fun n => a n s) (b s))
    {f : ℕ → MvPowerSeries σ C} {g : MvPowerSeries σ C} (h : TendsS V f g) :
    TendsS V (fun n => MvPowerSeries.subst (a n) (f n)) (MvPowerSeries.subst b g) := by
  have hA : MvPowerSeries.HasSubst fun s => (hab s).lift := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => ?_
    apply Subtype.ext
    refine Prod.ext (funext fun n => ha n s) ((hab s).const_zero fun n => ha n s)
  have h1 : ∀ n, MvPowerSeries.map (term V n) (MvPowerSeries.subst (fun s => (hab s).lift) h.lift) =
      MvPowerSeries.subst (a n) (f n) := fun n => MvPowerSeries.map_subst hA _
  have h2 : MvPowerSeries.map (lim V) (MvPowerSeries.subst (fun s => (hab s).lift) h.lift) =
      MvPowerSeries.subst b g := MvPowerSeries.map_subst hA _
  intro μ
  simp only [← h1, ← h2, MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff μ (MvPowerSeries.subst (fun s => (hab s).lift) h.lift)).2

theorem exists_tends (cpl : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n))
    {s : ℕ → C} (hs : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (s (n + 1) - s n)) : ∃ x, Tends V s x := by
  choose k hk using hs
  have hd : ∀ N m n, k N ≤ m → m ≤ n → V.Ge N (s n - s m) := by
    intro N m n hm hn
    induction n, hn using Nat.le_induction with
    | base => simpa using VF.Ge.zero (V := V) N
    | succ n hn ih => simpa using (hk N n (hm.trans hn)).add ih
  let φ : ℕ → ℕ := fun N => (Finset.range (N + 1)).sup k
  have h1 : ∀ N, k N ≤ φ N := fun N => Finset.le_sup (f := k) (Finset.self_mem_range_succ N)
  have h2 : ∀ N, φ N ≤ φ (N + 1) := fun N => Finset.sup_mono (Finset.range_mono (by omega))
  obtain ⟨x, hx⟩ := cpl (fun N => s (φ N)) fun N => hd N _ _ (h1 N) (h2 N)
  refine ⟨x, fun w => ?_⟩
  filter_upwards [eventually_ge_atTop (φ ⌈w⌉₊)] with n hn
  have := (hx ⌈w⌉₊).sub (hd ⌈w⌉₊ _ _ (h1 _) hn)
  simpa using this.mono (Nat.le_ceil w)

variable {dd : ℕ}

theorem const_ev {m n : ℕ} {a : Fin m → Pt C n dd} (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    {f : PS C m dd} (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (a := fun p : Fin m × Fin dd => a p.1 p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2) (fun p => ha p.1 p.2) hf

theorem const_of_ev {m n : ℕ} {a : Fin m → Pt C n dd} (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    {f : PS C m dd} (hf : ev a f = 0) : MvPowerSeries.constantCoeff f = 0 := by
  have h := const_ev ha (f := f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) (by simp)
  unfold ev at h hf
  rw [MvPowerSeries.subst_sub (a := fun p : Fin m × Fin dd => a p.1 p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2), hf,
    MvPowerSeries.subst_C] at h
  simpa using h

theorem const_pt {n : ℕ} (j : Fin n) (i : Fin dd) : MvPowerSeries.constantCoeff (pt C dd j i) = 0 := by
  simp [pt]

theorem const_comp1 {n : ℕ} {φ : Pt C 1 dd} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {a : Pt C n dd}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.constantCoeff (comp1 φ a i) = 0 :=
  const_ev (fun j i => by fin_cases j; exact ha i) (hφ i)

theorem tends_comp1 {n : ℕ} {φ : ℕ → Pt C 1 dd} {e : Pt C 1 dd} (h : ∀ i, TendsS V (fun k => φ k i) (e i))
    {a : Pt C n dd} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    TendsS V (fun k => comp1 (φ k) a i) (comp1 e a i) :=
  TendsS.subst (a := fun _ (p : Fin 1 × Fin dd) => ![a] p.1 p.2)
    (fun _ p => by obtain ⟨j, i⟩ := p; fin_cases j; exact ha i) (fun _ => TendsS.const _) (h i)

theorem constantCoeff_germEvalTwo_eq_zero {n : ℕ} {a b : Pt C n dd} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) {f : PS C 2 dd} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (ev ![a, b] f) = 0 :=
  const_ev (fun j i => by fin_cases j; exacts [ha i, hb i]) hf

theorem tendsToCoeffwise_germEvalTwo {n : ℕ} {a b : ℕ → Pt C n dd} {a' b' : Pt C n dd}
    (ha : ∀ k i, MvPowerSeries.constantCoeff (a k i) = 0) (hb : ∀ k i, MvPowerSeries.constantCoeff (b k i) = 0)
    (ha' : ∀ i, TendsS V (fun k => a k i) (a' i)) (hb' : ∀ i, TendsS V (fun k => b k i) (b' i)) (f : PS C 2 dd) :
    TendsS V (fun k => ev ![a k, b k] f) (ev ![a', b'] f) :=
  TendsS.subst (a := fun k (p : Fin 2 × Fin dd) => ![a k, b k] p.1 p.2)
    (fun k p => by obtain ⟨j, i⟩ := p; fin_cases j; exacts [ha k i, hb k i])
    (fun p => by obtain ⟨j, i⟩ := p; fin_cases j; exacts [ha' i, hb' i]) (TendsS.const f)

theorem exists_lim [CharZero C] {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) {a : ℕ → O}
    (ha : ActCv Y a) : ∃ e : Pt C 1 dd, ∀ i, TendsS V (fun n => Y.B.A.act (a n) i) (e i) := by
  choose e he using fun i μ => exists_tends Y.cpl (s := fun n => MvPowerSeries.coeff μ (Y.B.A.act (a n) i))
    fun N => ha N i μ
  exact ⟨fun i μ => e i μ, he⟩

theorem limit_endomorphisms : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O]
    (dd : ℕ) (Y : FBChart C V O dd), EndomorphismLimitIntegral Y := by
  intro C _ _ V O _ _ dd Y a ha hb
  obtain ⟨e, he⟩ := exists_lim Y ha
  obtain ⟨eb, heb⟩ := exists_lim Y hb
  have hc := Y.B.A.const
  refine ⟨e, eb, fun i μ => (he i μ).ge fun n => Y.intAct _ i μ, fun i μ => (heb i μ).ge fun n => Y.intAct _ i μ,
    fun N i μ => eventually_atTop.1 (he i μ N), fun N i μ => eventually_atTop.1 (heb i μ N), ?_, ?_⟩
  · funext i
    have h1 := tends_comp1 he (a := addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1))
      (fun i => constantCoeff_germEvalTwo_eq_zero (const_pt 0) (const_pt 1) (Y.B.G.const i)) i
    have h2 := tendsToCoeffwise_germEvalTwo (V := V) (fun k => const_comp1 (hc (a k)) (const_pt (n := 2) 0))
      (fun k => const_comp1 (hc (a k)) (const_pt 1)) (tends_comp1 he (const_pt 0))
      (tends_comp1 he (const_pt 1)) (Y.B.G.F i)
    refine h1.unique ?_
    simp only [Y.B.A.hom]
    exact h2
  · have hh : MvPowerSeries.constantCoeff Y.h = 0 :=
      const_of_ev (fun j i => by fin_cases j; exacts [map_zero _, const_pt 0 i]) Y.gauge.ax0
    have hid : ∀ {τ : Type} (f : MvPowerSeries τ C), MvPowerSeries.map (algebraMap C C) f = f := fun f => by
      ext μ; simp
    have hK : ∀ x, Y.B.actK C x = Y.B.A.act x := fun x => funext fun i => hid _
    have h1 := (tendsToCoeffwise_germEvalTwo (V := V) (fun k => const_comp1 (hc (a k)) (const_pt (n := 2) 0))
      (fun _ => const_pt 1) (tends_comp1 he (const_pt 0)) (fun i => TendsS.const _) Y.h).sub
      (tendsToCoeffwise_germEvalTwo (V := V) (fun _ => const_pt (n := 2) 0) (fun k => const_comp1 (hc (star (a k))) (const_pt 1))
        (fun i => TendsS.const _) (tends_comp1 heb (const_pt 1)) Y.h)
    have h2 := TendsS.subst (σ := Unit) (fun k _ => by
      rw [map_sub, constantCoeff_germEvalTwo_eq_zero (const_comp1 (hc (a k)) (const_pt (n := 2) 0)) (const_pt 1) hh,
        constantCoeff_germEvalTwo_eq_zero (const_pt (n := 2) 0) (const_comp1 (hc (star (a k))) (const_pt 1)) hh, sub_zero])
      (fun _ => h1) (TendsS.const (PowerSeries.exp C))
    intro μ
    refine (h2 μ).ge fun n => ?_
    have h3 := Y.gauge.ad (a n)
    rw [hK, hK] at h3
    have h4 := Y.intAd (a n) μ
    rw [(hid (Y.B.ad (a n))).symm.trans h3] at h4
    exact h4

end GlobalTheory.ActLimit
