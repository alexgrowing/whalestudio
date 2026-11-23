import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartFB

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Agr

variable {C : Type} [Field C]

def Agr {τ : Type} (k : ℕ) (f g : MvPowerSeries τ C) : Prop :=
  ∀ e : τ →₀ ℕ, e.degree < k → MvPowerSeries.coeff e f = MvPowerSeries.coeff e g

theorem Agr.symm {τ : Type} {k : ℕ} {f g : MvPowerSeries τ C} (h : Agr k f g) : Agr k g f :=
  fun e he => (h e he).symm

theorem Agr.trans {τ : Type} {k : ℕ} {f g g' : MvPowerSeries τ C} (h : Agr k f g) (h' : Agr k g g') : Agr k f g' :=
  fun e he => (h e he).trans (h' e he)

theorem Agr.add {τ : Type} {k : ℕ} {f g f' g' : MvPowerSeries τ C} (h : Agr k f g) (h' : Agr k f' g') :
    Agr k (f + f') (g + g') := fun e he => by rw [map_add, map_add, h e he, h' e he]

theorem agr_iff_trunc {τ : Type} [Finite τ] (k : ℕ) (f g : MvPowerSeries τ C) :
    Agr k f g ↔ MvPowerSeries.truncTotal k f = MvPowerSeries.truncTotal k g := by
  constructor
  · intro h
    ext e
    rw [MvPowerSeries.coeff_truncTotal_eq_ite, MvPowerSeries.coeff_truncTotal_eq_ite]
    split_ifs with he
    · exact h e he
    · rfl
  · intro h e he
    have h2 := congrArg (MvPolynomial.coeff e) h
    rwa [MvPowerSeries.coeff_truncTotal _ he, MvPowerSeries.coeff_truncTotal _ he] at h2

theorem agr_subst_left {σ τ : Type} [Finite σ] [Finite τ] {a b : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (hb : ∀ s, MvPowerSeries.constantCoeff (b s) = 0)
    {k : ℕ} (h : ∀ s, Agr k (a s) (b s)) (f : MvPowerSeries σ C) :
    Agr k (MvPowerSeries.subst a f) (MvPowerSeries.subst b f) := by
  have h' : ∀ s, MvPowerSeries.truncTotal k (a s) = MvPowerSeries.truncTotal k (b s) :=
    fun s => (agr_iff_trunc k _ _).1 (h s)
  rw [agr_iff_trunc, MvPowerSeries.truncTotal_subst ha, MvPowerSeries.truncTotal_subst hb]
  simp only [h']

theorem agr_subst_right {σ τ : Type} [Finite σ] [Finite τ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) {k : ℕ} {f g : MvPowerSeries σ C} (h : Agr k f g) :
    Agr k (MvPowerSeries.subst a f) (MvPowerSeries.subst a g) := by
  rw [agr_iff_trunc, MvPowerSeries.truncTotal_subst ha, MvPowerSeries.truncTotal_subst ha,
    (agr_iff_trunc k f g).1 h]

end Agr

section Wit

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def RawChart.TyWit (X : RawChart C d I κ) (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C)
    (γ : κ → PowerSeries C) (lam : JJ I g → PowerSeries C) : Prop :=
  IsCv V γ ∧ IsCv V lam ∧
    (∀ i : κ, alongCv γ (X.lg i) = ∑ c : I g, X.u g c i • tyS V.l (fun s => x s (Sum.inl c))) ∧
    ∀ q : JJ I g, tyS V.l (fun s => x s (Sum.inr q)) =
      lam q - alongCv γ (X.sg (X.u (1 - g) q)) +
        ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0

theorem RawChart.mem_tySet_iff (X : RawChart C d I κ) (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C) :
    x ∈ X.TySet V g ↔ ∃ γ lam, X.TyWit V g x γ lam := Iff.rfl

end Wit

def RankMaximalInitialCoefficient : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    (Y.raw p).RankHyp → ∀ Hc : ∀ g, (Y.raw p).CartHyp V g, (Y.raw p).AltC →
    ∀ (g : Fin 2) (a : ZMod d), (Y.raw p).big g a →
    ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (Hc g)).Good a w x →
    (∀ q, V.MM ((RawChart.cart (Hc g)).c0' x q)) →
    ∀ (γ : Fin dd → PowerSeries C) (lam : JJ I g → PowerSeries C), (Y.raw p).TyWit V g x γ lam →
      ∃ b : PS C 1 dd, IntS V b ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ
        (Y.chartLinearTerm (fun i => PowerSeries.coeff 1 (γ i)) -
          (ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] b - ev (n := 2) ![pt C dd 0] b -
            ev (n := 2) ![pt C dd 1] b)))

section MM

variable {C : Type} [Field C] {V : VF C}

theorem mm_zero : V.MM (0 : C) := by
  unfold VF.MM
  rw [AddValuation.map_zero]
  exact WithTop.coe_lt_top 0

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mm_mul_ge {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at hb
  rw [V.v.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa using hb
  exact lt_of_lt_of_le ha (le_add_of_nonneg_right hb')

theorem mm_sum {ι : Type} (s : Finset ι) (f : ι → C) (hf : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact mm_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact mm_add (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end MM

section Step2

variable {C : Type} [Field C]

theorem Agr.mono {τ : Type} {k k' : ℕ} {f g : MvPowerSeries τ C} (h : Agr k f g) (hk : k' ≤ k) : Agr k' f g :=
  fun e he => h e (lt_of_lt_of_le he hk)

theorem const_cvAt {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) {γ : PowerSeries C}
    (hγ : PowerSeries.constantCoeff γ = 0) : MvPowerSeries.constantCoeff (cvAt s γ) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hs) (fun _ => hs) hγ

theorem subst_cvAt {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) {σ : Type} [Finite σ]
    {γ : σ → PowerSeries C} (hγ : ∀ j, PowerSeries.constantCoeff (γ j) = 0) (F : MvPowerSeries σ C) :
    MvPowerSeries.subst (fun j => cvAt s (γ j)) F = cvAt s (MvPowerSeries.subst γ F) := by
  unfold cvAt
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hs)]

theorem cvAt_smul_X {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) (c : C) :
    cvAt s (c • (MvPowerSeries.X () : PowerSeries C)) = c • s := by
  unfold cvAt
  have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := Unit) fun _ => hs
  rw [MvPowerSeries.subst_smul hS, MvPowerSeries.subst_X hS]

theorem eval_points_two {dd : ℕ} (f : PS C 2 dd) : ev (n := 2) ![pt C dd 0, pt C dd 1] f = f := by
  unfold ev
  have e : (fun q : Fin 2 × Fin dd => (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) q.1 q.2) =
      fun q => (MvPowerSeries.X q : PS C 2 dd) := by
    funext ⟨k, j⟩
    fin_cases k <;> rfl
  rw [e, MvPowerSeries.subst_self]
  rfl

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem tyS_good_coeff {g : Fin 2} {w : I g → C} {x : ℕ → I g ⊕ JJ I g → C}
    (h0 : x 0 = Sum.elim w 0) (h1 : ∀ c, x 1 (Sum.inl c) = 0) (hl : 2 ≤ V.l) (c : I g) (n : ℕ)
    (hn : n < V.l ^ 2) :
    PowerSeries.coeff n (tyS V.l (fun s => x s (Sum.inl c))) = if n = 1 then w c else 0 := by
  unfold tyS
  rw [PowerSeries.coeff_mk, Finset.sum_eq_single 0]
  · rw [pow_zero]
    by_cases hn1 : n = 1
    · subst hn1
      rw [if_pos rfl, if_pos rfl]
      simp [h0]
    · have hn1' : ¬ (1 = n) := fun h => hn1 h.symm
      rw [if_neg hn1', if_neg hn1]
  · intro s _ hs0
    by_cases hs1 : s = 1
    · subst hs1
      simp [h1 c]
    · rw [if_neg]
      intro hsn
      have h2 : 2 ≤ s := by omega
      have h3 : V.l ^ 2 ≤ V.l ^ s := Nat.pow_le_pow_right (by omega) h2
      rw [hsn] at h3
      exact absurd hn (not_lt.mpr h3)
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos n)) h

theorem coeffX' (n : ℕ) : PowerSeries.coeff n (MvPowerSeries.X () : PowerSeries C) = if n = 1 then 1 else 0 :=
  PowerSeries.coeff_X n

theorem lgCv_agr (Y : FBChart C V O dd) (p : PairData Y d I) {g : Fin 2} {w : I g → C}
    {x : ℕ → I g ⊕ JJ I g → C} (h0 : x 0 = Sum.elim w 0) (h1 : ∀ c, x 1 (Sum.inl c) = 0)
    {γ : Fin dd → PowerSeries C}
    (hlg : ∀ i, alongCv γ ((Y.raw p).lg i) = ∑ c : I g, (Y.raw p).u g c i • tyS V.l (fun s => x s (Sum.inl c)))
    (i : Fin dd) :
    Agr (V.l ^ 2) (alongCv γ ((Y.raw p).lg i))
      ((∑ c, (Y.raw p).u g c i * w c) • (MvPowerSeries.X () : PowerSeries C)) := by
  intro e he
  have hl := V.l_prime.two_le
  rw [hlg i]
  obtain ⟨n, rfl⟩ : ∃ n, e = Finsupp.single () n := ⟨e (), Finsupp.unique_single e⟩
  rw [Finsupp.degree_single] at he
  change PowerSeries.coeff n _ = PowerSeries.coeff n _
  rw [map_sum, map_smul, coeffX']
  simp only [map_smul, smul_eq_mul, tyS_good_coeff h0 h1 hl _ n he]
  by_cases hn1 : n = 1
  · simp [hn1]
  · simp [hn1]

theorem lg_addOf (Y : FBChart C V O dd) {τ : Type} (P : Fin 2 → Fin dd → MvPowerSeries τ C)
    (hP : ∀ k j, MvPowerSeries.constantCoeff (P k j) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => MvPowerSeries.subst (fun q : Fin 2 × Fin dd => P q.1 q.2) (Y.B.G.F j))
        (un1 (Y.lg i)) =
      MvPowerSeries.subst (P 0) (un1 (Y.lg i)) + MvPowerSeries.subst (P 1) (un1 (Y.lg i)) := by
  have hPP : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd => P q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hP q.1 q.2
  have hF0 : ∀ j, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => P q.1 q.2) (Y.B.G.F j)) = 0 :=
    fun j => MvPowerSeries.constantCoeff_subst_eq_zero hPP (fun q => hP q.1 q.2) (Y.B.G.const j)
  rw [subst_singlePointUncurry hF0, subst_singlePointUncurry (hP 0), subst_singlePointUncurry (hP 1)]
  have key := congrArg (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => P q.1 q.2)) (Y.lg_add i)
  have hadd : addOf Y.B.G.F (pt C dd 0) (pt C dd 1) = Y.B.G.F := by
    funext j
    exact eval_points_two (Y.B.G.F j)
  have hA : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => Y.B.G.F q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => Y.B.G.const q.2
  have hX : ∀ k : Fin 2, MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => pt C (n := 2) dd k q.2) :=
    fun k => MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => MvPowerSeries.constantCoeff_X _
  rw [hadd, eval_single_eq_subst, eval_single_eq_subst, eval_single_eq_subst, MvPowerSeries.subst_add hPP,
    MvPowerSeries.subst_comp_subst_apply hA hPP, MvPowerSeries.subst_comp_subst_apply (hX 0) hPP,
    MvPowerSeries.subst_comp_subst_apply (hX 1) hPP] at key
  simp only [pt, MvPowerSeries.subst_X hPP] at key
  exact key

theorem ex_lg_at (Y : FBChart C V O dd) (p : PairData Y d I) {τ : Type} (A : Fin dd → MvPowerSeries τ C)
    (hA : ∀ j, MvPowerSeries.constantCoeff (A j) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => MvPowerSeries.subst A ((Y.raw p).lg j)) ((Y.raw p).ex i) = A i := by
  have hA' := MvPowerSeries.hasSubst_of_constantCoeff_zero hA
  have hL : MvPowerSeries.HasSubst (Y.raw p).lg :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => Y.chart_log_constantCoeff p j
  rw [← MvPowerSeries.subst_comp_subst_apply hL hA', Y.raw_exlg p, MvPowerSeries.subst_X hA']

theorem hom_of_good (Y : FBChart C V O dd) (p : PairData Y d I) {g : Fin 2} {w : I g → C}
    {x : ℕ → I g ⊕ JJ I g → C} (h0 : x 0 = Sum.elim w 0) (h1 : ∀ c, x 1 (Sum.inl c) = 0)
    {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ)
    (hlg : ∀ i, alongCv γ ((Y.raw p).lg i) = ∑ c : I g, (Y.raw p).u g c i • tyS V.l (fun s => x s (Sum.inl c)))
    (i : Fin dd) (μ : Fin 2 →₀ ℕ) (hμ0 : μ 0 < V.l) (hμ1 : μ 1 < V.l) :
    MvPowerSeries.coeff μ
      (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => cvAt (MvPowerSeries.X q.1) (γ q.2)) (Y.B.G.F i) -
        cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ i)) = 0 := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hX : ∀ k : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X k : MvPowerSeries (Fin 2) C) = 0 :=
    fun k => MvPowerSeries.constantCoeff_X k
  have hS : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) C) = 0 := by
    rw [map_add, hX 0, hX 1, add_zero]
  have hP0 : ∀ (k : Fin 2) (j : Fin dd), MvPowerSeries.constantCoeff (cvAt (MvPowerSeries.X k) (γ j)) = 0 :=
    fun k j => const_cvAt (hX k) (hγ0 j)
  have hQ0 : ∀ j, MvPowerSeries.constantCoeff (cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ j)) = 0 :=
    fun j => const_cvAt hS (hγ0 j)
  have hPP : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd => cvAt (MvPowerSeries.X q.1) (γ q.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hP0 q.1 q.2
  have hFP0 : ∀ j, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => cvAt (MvPowerSeries.X q.1) (γ q.2)) (Y.B.G.F j)) = 0 :=
    fun j => MvPowerSeries.constantCoeff_subst_eq_zero hPP (fun q => hP0 q.1 q.2) (Y.B.G.const j)
  have hAt : ∀ (s : MvPowerSeries (Fin 2) C), MvPowerSeries.constantCoeff s = 0 → ∀ j,
      Agr (V.l ^ 2) (MvPowerSeries.subst (fun j' => cvAt s (γ j')) ((Y.raw p).lg j))
        ((∑ c, (Y.raw p).u g c j * w c) • s) := by
    intro s hs j
    rw [subst_cvAt hs hγ0, ← cvAt_smul_X hs]
    exact agr_subst_right (a := fun _ : Unit => s) (fun _ => hs) (lgCv_agr Y p h0 h1 hlg j)
  have hsum : ∀ j, Agr (V.l ^ 2)
      (MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0) (γ j')) ((Y.raw p).lg j) +
        MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 1) (γ j')) ((Y.raw p).lg j))
      (MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ j')) ((Y.raw p).lg j)) := by
    intro j
    refine ((hAt _ (hX 0) j).add (hAt _ (hX 1) j)).trans ?_
    rw [← smul_add]
    exact (hAt _ hS j).symm
  have e1 := ex_lg_at Y p _ hFP0 i
  have e1' : (fun j => MvPowerSeries.subst
      (fun j' => MvPowerSeries.subst (fun q : Fin 2 × Fin dd => cvAt (MvPowerSeries.X q.1) (γ q.2)) (Y.B.G.F j'))
      ((Y.raw p).lg j)) = fun j =>
        MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0) (γ j')) ((Y.raw p).lg j) +
        MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 1) (γ j')) ((Y.raw p).lg j) := by
    funext j
    exact lg_addOf Y (fun k j' => cvAt (MvPowerSeries.X k) (γ j')) hP0 j
  rw [e1'] at e1
  have e2 := ex_lg_at Y p _ hQ0 i
  have hc : ∀ j, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0) (γ j')) ((Y.raw p).lg j) +
        MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 1) (γ j')) ((Y.raw p).lg j)) = 0 := by
    intro j
    rw [map_add, MvPowerSeries.constantCoeff_subst_eq_zero
        (MvPowerSeries.hasSubst_of_constantCoeff_zero fun j' => hP0 0 j') (fun j' => hP0 0 j') (Y.chart_log_constantCoeff p j),
      MvPowerSeries.constantCoeff_subst_eq_zero
        (MvPowerSeries.hasSubst_of_constantCoeff_zero fun j' => hP0 1 j') (fun j' => hP0 1 j') (Y.chart_log_constantCoeff p j),
      add_zero]
  have hc' : ∀ j, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ j')) ((Y.raw p).lg j)) = 0 :=
    fun j => MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero hQ0) hQ0 (Y.chart_log_constantCoeff p j)
  have hag := agr_subst_left hc hc' hsum ((Y.raw p).ex i)
  rw [e1, e2] at hag
  have hdeg : μ.degree < V.l ^ 2 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    nlinarith
  rw [map_sub, sub_eq_zero]
  exact hag μ hdeg

theorem coeff1_of_good (Y : FBChart C V O dd) (p : PairData Y d I) {g : Fin 2} {w : I g → C}
    {x : ℕ → I g ⊕ JJ I g → C} (h0 : x 0 = Sum.elim w 0) (h1 : ∀ c, x 1 (Sum.inl c) = 0)
    {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ)
    (hlg : ∀ i, alongCv γ ((Y.raw p).lg i) = ∑ c : I g, (Y.raw p).u g c i • tyS V.l (fun s => x s (Sum.inl c)))
    (i : Fin dd) : PowerSeries.coeff 1 (γ i) = ∑ c, (Y.raw p).u g c i * w c := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hlin : Agr 2 ((Y.raw p).lg i) (MvPowerSeries.X i) := fun e he =>
    Y.raw_lin p i e (by omega)
  have h2 := agr_subst_right (a := γ) hγ0 hlin
  rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0)] at h2
  have h3 := (lgCv_agr Y p h0 h1 hlg i).mono (show 2 ≤ V.l ^ 2 by nlinarith)
  have h4 := (h2.symm.trans h3) (Finsupp.single () 1) (by rw [Finsupp.degree_single]; omega)
  change PowerSeries.coeff 1 (γ i) = PowerSeries.coeff 1 _ at h4
  rw [h4, map_smul, coeffX', if_pos rfl, smul_eq_mul, mul_one]

end Step2

theorem rank_maximal_of_nondegenerate (h1 : RankMaximalInitialCoefficient) : RankMaximalOfNondegenerate := by
  intro C _ _ V O _ _ dd Y d _ I _ p hN hrk Hc hAlt g a hbig w x hG hc0 c
  by_contra hwc
  obtain ⟨γ, lam, hW⟩ := ((Y.raw p).mem_tySet_iff V g x).1 hG.1.1
  obtain ⟨b, hb, hbc⟩ := h1 C V O dd Y d I p hrk Hc hAlt g a hbig w x hG hc0 γ lam hW
  refine hN γ hW.1 ?_ ?_ ⟨b, hb, hbc⟩
  · by_contra hall
    push Not at hall
    apply hwc
    obtain ⟨wd, hwd, hsat⟩ := p.u_sat g
    have hU : ∀ i, V.MM (∑ c', (Y.raw p).u g c' i * w c') := fun i => by
      rw [← coeff1_of_good Y p hG.1.2.1 hG.2 hW.1 hW.2.2.1 i]
      exact hall i
    have e : w c = ∑ i, (∑ c', (Y.raw p).u g c' i * w c') * wd i c := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      have : ∀ c', ∑ i, (Y.raw p).u g c' i * w c' * wd i c = w c' * (if c' = c then 1 else 0) := by
        intro c'
        rw [← hsat c' c, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        show p.u g c' i * w c' * wd i c = w c' * (p.u g c' i * wd i c)
        ring
      simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [e]
    exact mm_sum _ _ fun i _ => mm_mul_ge (hU i) (hwd i c)
  · intro i μ hμ0 hμ1
    rw [hom_of_good Y p hG.1.2.1 hG.2 hW.1 hW.2.2.1 i μ hμ0 hμ1]
    exact mm_zero

end Formalism.L2.FormalSeriesBounds
