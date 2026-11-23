import Formalism.LocalToGlobal.CharacterGerms.RowTiePIndAr
import Formalism.LocalToGlobal.CharacterGerms.RowTiePAddCvSelf

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

def PTExSelfSt : Prop :=
  AllSelf fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) →
    (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) →
    ∃ x ∈ X.TySet V g, ∀ c, x 0 (Sum.inl c) = w c

def PTAvgSelfSt : Prop :=
  AllSelf fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (x : ℕ → I g ⊕ JJ I g → C), x ∈ X.TySet V g →
    (∀ n, X.tyC g n ≠ a → x 0 n = 0) →
    ∃ x' ∈ X.TySet V g, x' 0 = x 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x' i n = 0

def OActSelfSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0)
    (g : Fin 2) (α : O) (x : ℕ → I0 ⊕ I0 → C), x ∈ (Y.rawSelf p).TySet V g →
    (fun s n => p.em ((Y.rawSelf p).tyC g n) α * x s n) ∈ (Y.rawSelf p).TySet V g

def LimSelfSt : Prop :=
  AllSelf fun C _ V _ I _ _ X => ∀ (g : Fin 2) (x : ℕ → ℕ → I g ⊕ JJ I g → C) (x' : ℕ → I g ⊕ JJ I g → C),
    (∀ k, x k ∈ X.TySet V g) → VLim V x x' → x' ∈ X.TySet V g

private theorem ge_zero_mul_field {C : Type} [Field C] (V : VF C) {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) :
    V.Ge 0 (a * b) := by
  unfold VF.Ge at *
  rw [V.v.map_mul]
  simp only [WithTop.coe_zero] at *
  exact add_nonneg ha hb

private theorem ge_zero_finset_sum_field {C : Type} [Field C] (V : VF C) {ι : Type} (s : Finset ι) (f : ι → C)
    (h : ∀ i ∈ s, V.Ge 0 (f i)) : V.Ge 0 (∑ i ∈ s, f i) := by
  refine Finset.sum_induction f (fun z => V.Ge 0 z) (fun a b ha hb => ?_) ?_ h
  · exact le_trans (le_min ha hb) (V.v.map_add a b)
  · show ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
    rw [AddValuation.map_zero]
    exact le_top

private theorem tyS_sub_ite_zero_eq_sub_C_mul_X {C : Type} [Field C] (l : ℕ) (a : ℕ → C) (c : C) :
    tyS l (fun s => a s - if s = 0 then c else 0) = tyS l a - PowerSeries.C c * PowerSeries.X := by
  ext m
  rw [map_sub, ← pow_one (PowerSeries.X : PowerSeries C), PowerSeries.coeff_C_mul_X_pow]
  simp only [tyS, PowerSeries.coeff_mk]
  have h1 : ∀ s, (if l ^ s = m then a s - (if s = 0 then c else 0) else 0) =
      (if l ^ s = m then a s else 0) - (if s = 0 then (if m = 1 then c else 0) else 0) := by
    intro s
    by_cases hs : s = 0
    · subst hs
      by_cases hm : m = 1
      · subst hm
        simp
      · have hm' : (1 : ℕ) ≠ m := fun h => hm h.symm
        simp [hm, hm']
    · simp [hs]
  rw [Finset.sum_congr rfl (fun s _ => h1 s), Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp

theorem ptSelf_of (hEx : PTExSelfSt) (hAvg : PTAvgSelfSt) (hStab : HStabSelfSt) : PTSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g a w hw hty
  obtain ⟨x, hx, hx0⟩ := hEx C V O dd Y d I0 p g a w hw hty
  obtain ⟨γ, lam, hγ, hlam, hlg, hq⟩ := hx
  have hl1 : V.l ≠ 1 := V.l_prime.one_lt.ne'
  have hγ0 : ∀ i, ∀ m < 1, PowerSeries.coeff m (γ i) = 0 := by
    intro i m hm
    rw [Nat.lt_one_iff.mp hm, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hγ i).1
  have c1 : ∀ f : ℕ → C, PowerSeries.coeff 1 (tyS V.l f) = f 0 := by
    intro f
    simp [tyS, PowerSeries.coeff_mk, Finset.sum_range_succ, hl1]
  have hdeg : ∀ j : Fin 2 × Fin dd, (Finsupp.single j 1).degree ≤ 1 := by
    intro j
    first
    | simp [Finsupp.degree_single]
    | (unfold Finsupp.degree; simp)
  have hγ1 : ∀ i, PowerSeries.coeff 1 (γ i) = ∑ c, (Y.rawSelf p).u g c i * w c := by
    intro i
    have h1 := congrArg (PowerSeries.coeff 1) (hlg i)
    rw [coeff_alongCv_low le_rfl hγ0 (FBChart.self_chart_log_constantCoeff (Y := Y) (p := p) i), map_sum] at h1
    simp only [PowerSeries.coeff_smul, c1, hx0, smul_eq_mul] at h1
    rw [← h1, Finset.sum_eq_single i]
    · rw [FBChart.rawSelf_lin (Y := Y) (p := p) i _ (hdeg i), MvPowerSeries.coeff_X, if_pos rfl, one_mul]
    · intro j _ hji
      rw [FBChart.rawSelf_lin (Y := Y) (p := p) i _ (hdeg j), MvPowerSeries.coeff_X, if_neg, zero_mul]
      intro h
      exact hji (Finsupp.single_left_injective one_ne_zero h)
    · intro h
      exact absurd (Finset.mem_univ i) h
  have key : ∀ q : I0, V.Ge 0 (PowerSeries.coeff 1 (lam q) - x 0 (Sum.inr q)) := by
    intro q
    have h2 := congrArg (PowerSeries.coeff 1) (hq q)
    rw [c1, map_add, map_sub, map_sum,
      coeff_alongCv_low le_rfl hγ0 (RawChart.constantCoeff_sg (Y.rawSelf p) (fun e he => FBChart.rawSelf_axis0 (Y := Y) (p := p) e he) _)] at h2
    simp only [hγ1] at h2
    have hA : ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) ((Y.rawSelf p).sg ((Y.rawSelf p).u (1 - g) q)) *
        ∑ c, (Y.rawSelf p).u g c i * w c =
        ∑ c, w c * (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) := by
      simp only [RawChart.sg1, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun i _ => by ring))
    rw [hA] at h2
    have hS : ∀ c, PowerSeries.coeff 1 (if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then
        (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c))
        else 0) = if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then
        (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) * w c else 0 := by
      intro c
      split_ifs
      · simp only [PowerSeries.coeff_smul, c1, hx0, smul_eq_mul]
      · exact map_zero _
    simp only [hS] at h2
    have h3 : PowerSeries.coeff 1 (lam q) - x 0 (Sum.inr q) =
        ∑ c, if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then 0 else
          w c * (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) := by
      rw [h2, show ∀ L A S : C, L - (L - A + S) = A - S from fun L A S => by ring, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      split_ifs <;> ring
    rw [h3]
    refine ge_zero_finset_sum_field V _ _ (fun c _ => ?_)
    split_ifs with hne
    · show ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
      rw [AddValuation.map_zero]
      exact le_top
    · exact ge_zero_mul_field V (hw c) (hStab C V O dd Y d I0 p g c q hne)
  have hyT : (fun s n => Sum.elim (fun c => x s (Sum.inl c))
      (fun q => x s (Sum.inr q) - if s = 0 then x 0 (Sum.inr q) else 0) n : ℕ → I0 ⊕ I0 → C) ∈
      (Y.rawSelf p).TySet V g := by
    refine ⟨γ, fun q => lam q - PowerSeries.C (x 0 (Sum.inr q)) * PowerSeries.X, hγ, ?_, ?_, ?_⟩
    · intro q
      refine ⟨?_, ?_⟩
      · simp [(hlam q).1]
      · intro m
        rcases eq_or_ne m 1 with rfl | hm
        · have h4 : PowerSeries.coeff 1 (lam q - PowerSeries.C (x 0 (Sum.inr q)) * PowerSeries.X) =
              PowerSeries.coeff 1 (lam q) - x 0 (Sum.inr q) := by
            simp
          rw [h4]
          exact key q
        · have h4 : PowerSeries.coeff m (lam q - PowerSeries.C (x 0 (Sum.inr q)) * PowerSeries.X) =
              PowerSeries.coeff m (lam q) := by
            rw [map_sub, ← pow_one (PowerSeries.X : PowerSeries C), PowerSeries.coeff_C_mul_X_pow, if_neg hm,
              sub_zero]
          rw [h4]
          exact (hlam q).2 m
    · intro i
      exact hlg i
    · intro q
      show tyS V.l (fun s => x s (Sum.inr q) - if s = 0 then x 0 (Sum.inr q) else 0) =
        (lam q - PowerSeries.C (x 0 (Sum.inr q)) * PowerSeries.X) -
          alongCv γ ((Y.rawSelf p).sg ((Y.rawSelf p).u (1 - g) q)) +
          ∑ c, if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then
            (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c))
            else 0
      rw [tyS_sub_ite_zero_eq_sub_C_mul_X, hq q]
      ring
  obtain ⟨x', hx', h0, hvan⟩ := hAvg C V O dd Y d I0 p g a _ hyT (by
    intro n hn
    rcases n with c | q
    · show x 0 (Sum.inl c) = 0
      rw [hx0]
      exact hty c hn
    · show x 0 (Sum.inr q) - (if (0 : ℕ) = 0 then x 0 (Sum.inr q) else 0) = 0
      simp)
  refine ⟨x', hx', ?_, hvan⟩
  rw [h0]
  funext n
  rcases n with c | q
  · exact hx0 c
  · show x 0 (Sum.inr q) - (if (0 : ℕ) = 0 then x 0 (Sum.inr q) else 0) = 0
    simp

theorem ptAvgSelf_of (hAct : OActSelfSt) (hLim : LimSelfSt) : PTAvgSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g a x hx hx0
  set X := Y.rawSelf p with hX
  let M : Set (ℕ → I0 ⊕ I0 → C) := {m | ∀ y ∈ X.TySet V g, m * y ∈ X.TySet V g}
  have hAdd := addCvSelf_holds C V O dd Y d I0 p
  have h1 : (1 : ℕ → I0 ⊕ I0 → C) ∈ M := fun y hy => by rwa [one_mul]
  have hadd : ∀ m m', m ∈ M → m' ∈ M → m + m' ∈ M := fun m m' hm hm' y hy => by
    rw [add_mul]; exact X.add_mem V g hAdd (fun g c x => Y.rawSelf_u_integral p g c x) _ _ (hm y hy) (hm' y hy)
  have hneg : ∀ m, m ∈ M → -m ∈ M := fun m hm y hy => by
    rw [neg_mul]; exact X.neg_mem V g Y.l_odd _ (hm y hy)
  have hmul : ∀ m m', m ∈ M → m' ∈ M → m * m' ∈ M := fun m m' hm hm' y hy => by
    rw [mul_assoc]; exact hm _ (hm' y hy)
  have hteich : ∀ c : C, V.Ge 0 c → (fun s (_ : I0 ⊕ I0) => c ^ (V.l ^ s)) ∈ M := fun c hc y hy =>
    X.teich_mem V g c hc y hy
  have hact : ∀ α : O, (fun (_ : ℕ) n => p.em (X.tyC g n) α) ∈ M := fun α y hy =>
    hAct C V O dd Y d I0 p g α y hy
  have hlim : ∀ (m : ℕ → ℕ → I0 ⊕ I0 → C) (m' : ℕ → I0 ⊕ I0 → C), (∀ k, m k ∈ M) → VLim V m m' → m' ∈ M :=
    fun m m' hm hmm' y hy => hLim C V O dd Y d I0 p g (fun k => m k * y) (m' * y) (fun k => hm k y hy) (hmm'.mul_right y)
  have hI := IndAr.ind_gen p.em p.em_int p.em_frob p.em_sep (I0 ⊕ I0) (X.tyC g) M h1 hadd hneg hmul hteich hact hlim a
  refine ⟨_, hI x hx, ?_, ?_⟩
  · funext n
    simp only [Pi.mul_apply, Nat.cast_zero, add_zero]
    by_cases hn : X.tyC g n = a
    · rw [if_pos hn, one_mul]
    · rw [if_neg hn, zero_mul, hx0 n hn]
  · intro i n hn
    simp only [Pi.mul_apply]
    rw [if_neg hn, zero_mul]

theorem ptSelf_of_act (hEx : PTExSelfSt) (hAct : OActSelfSt) (hLim : LimSelfSt) (hStab : HStabSelfSt) : PTSelfSt :=
  ptSelf_of hEx (ptAvgSelf_of hAct hLim) hStab

theorem ptExSelf_of_pt (h : PTSelfSt) : PTExSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g a w hw hty
  obtain ⟨x, hx, h0, -⟩ := h C V O dd Y d I0 p g a w hw hty
  exact ⟨x, hx, fun c => congrFun h0 (Sum.inl c)⟩

end Formalism.L2.FormalSeriesBounds
