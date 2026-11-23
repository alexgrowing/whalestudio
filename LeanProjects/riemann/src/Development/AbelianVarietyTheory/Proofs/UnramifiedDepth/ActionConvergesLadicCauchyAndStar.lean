import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.ActionLimit

open MvPowerSeries GlobalTheory.GaugeAdjoint

section Bound

variable {C : Type} [Field C] {V : VF C} {σ τ : Type}

def Low (V : VF C) (D : ℕ) (w : ℝ) (g : MvPowerSeries τ C) : Prop :=
  ∀ μ : τ →₀ ℕ, μ.degree ≤ D → V.Ge w (coeff μ g)

theorem Low.mono {D : ℕ} {w w' : ℝ} {g : MvPowerSeries τ C} (h : Low V D w g) (hw : w' ≤ w) :
    Low V D w' g := fun μ hμ => (h μ hμ).mono hw

theorem low_of_int {g : MvPowerSeries τ C} (h : IntS V g) (D : ℕ) : Low V D 0 g := fun μ _ => h μ

theorem low_zero (D : ℕ) (w : ℝ) : Low V D w (0 : MvPowerSeries τ C) := fun μ _ => by
  simpa using VF.Ge.zero (V := V) w

theorem low_one (D : ℕ) : Low V D 0 (1 : MvPowerSeries τ C) := fun μ _ => by
  classical
  rw [coeff_one]
  split_ifs
  exacts [VF.Ge.one, VF.Ge.zero 0]

theorem Low.add {D : ℕ} {w : ℝ} {g h : MvPowerSeries τ C} (hg : Low V D w g) (hh : Low V D w h) :
    Low V D w (g + h) := fun μ hμ => by
  rw [map_add]; exact (hg μ hμ).add (hh μ hμ)

theorem Low.mul {D : ℕ} {w w' : ℝ} {g h : MvPowerSeries τ C} (hg : Low V D w g) (hh : Low V D w' h) :
    Low V D (w + w') (g * h) := fun μ hμ => by
  classical
  rw [coeff_mul]
  refine VF.Ge.sum fun p hp => ?_
  have e : p.1.degree + p.2.degree = μ.degree := by
    rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
  exact (hg _ (by omega)).mul (hh _ (by omega))

def Cong (V : VF C) (D : ℕ) (w : ℝ) (g h : MvPowerSeries τ C) : Prop :=
  Low V D 0 g ∧ Low V D 0 h ∧ Low V D w (g - h)

theorem cong_one (D : ℕ) (w : ℝ) : Cong V D w (1 : MvPowerSeries τ C) 1 :=
  ⟨low_one D, low_one D, by simpa using low_zero D w⟩

theorem Cong.mul {D : ℕ} {w : ℝ} {g h g' h' : MvPowerSeries τ C} (h1 : Cong V D w g h)
    (h2 : Cong V D w g' h') : Cong V D w (g * g') (h * h') := by
  refine ⟨by simpa using h1.1.mul h2.1, by simpa using h1.2.1.mul h2.2.1, ?_⟩
  have e : g * g' - h * h' = (g - h) * g' + h * (g' - h') := by ring
  rw [e]
  exact Low.add (by simpa using h1.2.2.mul h2.1) (by simpa using h1.2.1.mul h2.2.2)

theorem Cong.pow {D : ℕ} {w : ℝ} {g h : MvPowerSeries τ C} (h1 : Cong V D w g h) (n : ℕ) :
    Cong V D w (g ^ n) (h ^ n) := by
  induction n with
  | zero => simpa using cong_one D w
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h1

theorem cong_prod {D : ℕ} {w : ℝ} {a b : σ → MvPowerSeries τ C} (h : ∀ s, Cong V D w (a s) (b s))
    (e : σ →₀ ℕ) : Cong V D w (e.prod fun s n => a s ^ n) (e.prod fun s n => b s ^ n) := by
  classical
  unfold Finsupp.prod
  induction e.support using Finset.induction_on with
  | empty => simpa using cong_one D w
  | insert s S hs ih =>
    rw [Finset.prod_insert hs, Finset.prod_insert hs]
    exact ((h s).pow _).mul ih

theorem coeff_prod_high {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (e : σ →₀ ℕ) (μ : τ →₀ ℕ) (h : μ.degree < e.degree) :
    coeff μ (e.prod fun s n => a s ^ n) = 0 := by
  classical
  apply coeff_of_lt_order
  have key : ∀ S : Finset σ, ((∑ s ∈ S, e s : ℕ) : ℕ∞) ≤ (∏ s ∈ S, a s ^ e s).order := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert s S hs ih =>
      rw [Finset.prod_insert hs, Finset.sum_insert hs, Nat.cast_add]
      exact le_trans (add_le_add (le_order_pow_of_constantCoeff_eq_zero _ (ha s)) ih) le_order_mul
  refine lt_of_lt_of_le ?_ (key e.support)
  exact_mod_cast h

theorem low_subst_sub [Finite σ] {D : ℕ} {w c : ℝ} {a b : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    (h : ∀ s, Cong V D w (a s) (b s)) {f : MvPowerSeries σ C} (hf : Low V D c f) :
    Low V D (c + w) (subst a f - subst b f) := by
  intro μ hμ
  have hs := hasSubst_of_constantCoeff_zero ha
  have hs' := hasSubst_of_constantCoeff_zero hb
  rw [map_sub, coeff_subst hs, coeff_subst hs',
    ← finsum_sub_distrib (coeff_subst_finite hs f μ) (coeff_subst_finite hs' f μ)]
  refine finsum_induction (fun x => V.Ge (c + w) x) (VF.Ge.zero _) (fun _ _ => VF.Ge.add) fun e => ?_
  by_cases he : e.degree ≤ D
  · rw [← smul_sub, ← map_sub, smul_eq_mul]
    exact (hf e he).mul ((cong_prod h e).2.2 μ hμ)
  · rw [coeff_prod_high ha e μ (by omega), coeff_prod_high hb e μ (by omega)]
    simpa using VF.Ge.zero (V := V) (c + w)

theorem exists_ge (V : VF C) (x : C) : ∃ c : ℝ, V.Ge c x := by
  unfold VF.Ge
  induction V.v x using WithTop.recTopCoe with
  | top => exact ⟨0, le_top⟩
  | coe t => exact ⟨t, le_rfl⟩

theorem exists_low (V : VF C) [Finite τ] {ι : Type} [Finite ι] (D : ℕ) (f : ι → MvPowerSeries τ C) :
    ∃ c : ℝ, ∀ i, Low V D c (f i) := by
  have hfin : {μ : τ →₀ ℕ | μ.degree ≤ D}.Finite := Finsupp.finite_of_degree_le D
  haveI := hfin.to_subtype
  choose c hc using fun p : ι × {μ : τ →₀ ℕ | μ.degree ≤ D} => exists_ge V (coeff p.2.1 (f p.1))
  obtain ⟨m, hm⟩ := (Set.finite_range c).bddBelow
  exact ⟨m, fun i μ hμ => (hc (i, ⟨μ, hμ⟩)).mono (hm ⟨_, rfl⟩)⟩

theorem Low.l_pow {D : ℕ} {w : ℝ} {g : MvPowerSeries τ C} (h : Low V D w g) (n : ℕ) :
    Low V D (n + w) (V.l ^ n • g) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    intro μ hμ
    have := (ih μ hμ).l_mul
    rw [pow_succ', mul_smul, map_nsmul, nsmul_eq_mul]
    refine this.mono (le_of_eq ?_)
    push_cast; ring

end Bound

section Log

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)

theorem lg_const (i : Fin dd) : constantCoeff (Y.lg i) = 0 := by
  have := Y.lg_lin i 0 (by simp)
  simpa using this

theorem log_act_add (a b : O) :
    comp1 Y.lg (Y.B.A.act (a + b)) = comp1 Y.lg (Y.B.A.act a) + comp1 Y.lg (Y.B.A.act b) := by
  funext i
  have hab := const_two (Y.B.A.const a) (Y.B.A.const b)
  have h := congrArg (ev (n := 1) ![Y.B.A.act a, Y.B.A.act b]) (Y.lg_add i)
  have hF : ∀ j, constantCoeff (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C dd 1) j) = 0 := fun j => by
    rw [addOf, constantCoeff_ev (const_two (const_pt 0) (const_pt 1)), Y.B.G.const]
  have e0 : (fun j => ev (n := 1) ![Y.B.A.act a, Y.B.A.act b] (pt C dd (0 : Fin 2) j)) = Y.B.A.act a :=
    funext fun j => ev_pt hab 0 j
  have e1 : (fun j => ev (n := 1) ![Y.B.A.act a, Y.B.A.act b] (pt C dd (1 : Fin 2) j)) = Y.B.A.act b :=
    funext fun j => ev_pt hab 1 j
  have e2 : (fun j => ev (n := 1) ![Y.B.A.act a, Y.B.A.act b]
      (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C dd 1) j)) = Y.B.A.act (a + b) := by
    funext j
    rw [addOf, ev_ev_two (const_pt 0) (const_pt 1) hab, e0, e1, Y.B.A.add_act]
    rfl
  have hadd : ∀ f g : PS C 2 dd, ev (n := 1) ![Y.B.A.act a, Y.B.A.act b] (f + g) =
      ev (n := 1) ![Y.B.A.act a, Y.B.A.act b] f + ev (n := 1) ![Y.B.A.act a, Y.B.A.act b] g :=
    fun f g => subst_add (hasSubst_pts hab) f g
  rw [hadd, ev_ev_one hF hab, ev_ev_one (const_pt 0) hab, ev_ev_one (const_pt 1) hab, e0, e1, e2] at h
  exact h

noncomputable def logAct : O →+ Pt C 1 dd :=
  AddMonoidHom.mk' (fun a => comp1 Y.lg (Y.B.A.act a)) (log_act_add Y)

theorem logAct_const (a : O) (i : Fin dd) : constantCoeff (logAct Y a i) = 0 :=
  const_comp1 (lg_const Y) (Y.B.A.const a) i

theorem act_eq (a : O) : Y.B.A.act a = comp1 Y.ex (logAct Y a) := by
  funext i
  have ha := const_one (Y.B.A.const a)
  have h := congrArg (ev (n := 1) ![Y.B.A.act a]) (congrFun Y.ex_lg i)
  rw [comp1, ev_ev_one (lg_const Y) ha, ev_pt ha] at h
  exact h.symm

omit [CharZero C] in
theorem low_ev_sub {D m n : ℕ} {w c : ℝ} {x y : Fin m → Pt C n dd} {f : PS C m dd}
    (hx : ∀ j i, constantCoeff (x j i) = 0) (hy : ∀ j i, constantCoeff (y j i) = 0)
    (h : ∀ j i, Cong V D w (x j i) (y j i)) (hf : Low V D c f) :
    Low V D (c + w) (ev x f - ev y f) :=
  low_subst_sub (a := fun p : Fin m × Fin dd => x p.1 p.2) (b := fun p : Fin m × Fin dd => y p.1 p.2)
    (fun s => hx s.1 s.2) (fun s => hy s.1 s.2) (fun s => h s.1 s.2) hf

omit [CharZero C] in
theorem low_comp1_sub {D : ℕ} {w c : ℝ} {x y φ : Pt C 1 dd}
    (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0)
    (h : ∀ i, Cong V D w (x i) (y i)) (hφ : ∀ i, Low V D c (φ i)) (i : Fin dd) :
    Low V D (c + w) (comp1 φ x i - comp1 φ y i) := by
  refine low_ev_sub (const_one hx) (const_one hy) (fun j s => ?_) (hφ i)
  fin_cases j
  exact h s

omit [CharZero C] in
theorem cong_zero_of_int {D : ℕ} {τ : Type} {g h : MvPowerSeries τ C} (hg : IntS V g) (hh : IntS V h) :
    Cong V D 0 g h :=
  ⟨low_of_int hg D, low_of_int hh D, fun μ _ => by rw [map_sub]; exact (hg μ).sub (hh μ)⟩

theorem exists_low_logAct (D : ℕ) : ∃ c : ℝ, ∀ y i, Low V D c (logAct Y y i) := by
  obtain ⟨c, hc⟩ := exists_low V D Y.lg
  refine ⟨c, fun y i => ?_⟩
  have h := low_comp1_sub (Y.B.A.const y) (Y.B.A.const 0)
    (fun j => cong_zero_of_int (D := D) (Y.intAct y j) (Y.intAct 0 j)) hc i
  change Low V D (c + 0) (logAct Y y i - logAct Y 0 i) at h
  simpa using h

theorem act_small (D N : ℕ) : ∃ n0 : ℕ, ∀ n ≥ n0, ∀ (y : O) i,
    Low V D N (Y.B.A.act ((V.l : O) ^ n * y) i - Y.B.A.act 0 i) := by
  obtain ⟨c, hc⟩ := exists_low_logAct Y D
  obtain ⟨c', hc'⟩ := exists_low V D Y.ex
  obtain ⟨n0, hn0⟩ := exists_nat_ge (max (-c) (N - c - c'))
  refine ⟨n0, fun n hn y i => ?_⟩
  have hn' : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := le_max_left (-c) (N - c - c')
  have h2 := le_max_right (-c) (N - c - c')
  have hL : ∀ j, Low V D (n + c) (logAct Y ((V.l : O) ^ n * y) j) := fun j => by
    rw [← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul]
    exact (hc y j).l_pow n
  rw [act_eq, act_eq Y 0]
  refine (low_comp1_sub (w := n + c) (logAct_const Y _) (logAct_const Y _) (fun j => ?_) hc' i).mono
    (by linarith)
  rw [map_zero]
  exact ⟨(hL j).mono (by linarith), low_zero _ _, by simpa using hL j⟩

theorem actCv (a : ℕ → O) (ha : ∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) : ActCv Y a := by
  intro N i μ
  obtain ⟨n0, hn0⟩ := act_small Y μ.degree N
  refine ⟨n0, fun n hn => ?_⟩
  obtain ⟨y, hy⟩ := ha n
  have e1 : Y.B.A.act (a (n + 1)) = addOf Y.B.G.F (Y.B.A.act (a n)) (Y.B.A.act ((V.l : O) ^ n * y)) := by
    have := Y.B.A.add_act (a n) ((V.l : O) ^ n * y)
    rwa [← hy, add_sub_cancel, hy] at this
  have e0 : Y.B.A.act (a n) = addOf Y.B.G.F (Y.B.A.act (a n)) (Y.B.A.act 0) := by
    have := Y.B.A.add_act (a n) 0
    rwa [add_zero] at this
  have h : Low V μ.degree (0 + N) (addOf Y.B.G.F (Y.B.A.act (a n)) (Y.B.A.act ((V.l : O) ^ n * y)) i -
      addOf Y.B.G.F (Y.B.A.act (a n)) (Y.B.A.act 0) i) := by
    refine low_ev_sub (const_two (Y.B.A.const _) (Y.B.A.const _))
      (const_two (Y.B.A.const _) (Y.B.A.const _)) (fun j s => ?_) (low_of_int (Y.intF i) _)
    fin_cases j
    · exact ⟨low_of_int (Y.intAct _ s) _, low_of_int (Y.intAct _ s) _, by simpa using low_zero _ _⟩
    · exact ⟨low_of_int (Y.intAct _ s) _, low_of_int (Y.intAct _ s) _, hn0 n hn y s⟩
  rw [← e1, ← e0, zero_add] at h
  rw [← map_sub]
  exact h μ le_rfl

end Log

theorem main : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (a : ℕ → O), (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) →
    ActCv Y a ∧ ActCv Y (fun n => star (a n)) := by
  intro C _ _ V O _ _ dd Y a ha
  refine ⟨actCv Y a ha, actCv Y _ fun n => ?_⟩
  obtain ⟨y, hy⟩ := ha n
  exact ⟨star y, by rw [← star_sub, hy, star_mul', star_pow, star_natCast]⟩

end GlobalTheory.ActionLimit
