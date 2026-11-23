import Formalism.LocalToGlobal.CharacterGerms.BlockMembershipSelfConjugate

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds

section Jet

variable {C : Type} [Field C] {σ : Type}

theorem cc_mvExp (x : MvPowerSeries σ C) : MvPowerSeries.constantCoeff (mvExp x) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ k ∈ Finset.range ((0 : σ →₀ ℕ).degree + 1), MvPowerSeries.coeff 0 (x ^ k) / (k.factorial : C)) = 1
  simp

theorem jetAt0_one (G : MvPowerSeries σ C) : jetAt0 (1 : MvPolynomial σ C) G = MvPowerSeries.constantCoeff G := by
  unfold jetAt0
  rw [MvPolynomial.support_one, Finset.sum_singleton]
  simp [mfact]

end Jet

section Par

theorem odd_sub_val {d : ℕ} [NeZero d] (hd : Even d) (x y : ZMod d) (h : ¬ (Even x.val ↔ Even y.val)) :
    Odd (y - x).val := by
  have h2 : 2 ∣ d := hd.two_dvd
  have e : y = x + (y - x) := by ring
  have e1 : y.val = (x.val + (y - x).val) % d := by
    conv_lhs => rw [e]
    exact ZMod.val_add _ _
  have e2 : y.val % 2 = (x.val + (y - x).val) % 2 := by rw [e1, Nat.mod_mod_of_dvd _ h2]
  rw [Nat.even_iff, Nat.even_iff] at h
  rw [Nat.odd_iff]
  omega

end Par

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  (X : RowData C V d I J) (F : Flag X)

theorem vars_letter {g : Fin 2} {a : ZMod d} {N : ℕ} {Q : MvPolynomial (Fin N × Fin (X.rkF g a)) C} {ρ : Fin N} {w : WV I}
    (h : (ρ, w) ∈ (MvPolynomial.rename (F.letter g a) Q).vars) : w.1 = g ∧ tyW X.G w = a := by
  obtain ⟨x, -, e⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ h)
  have e2 : (⟨g, F.en g a x.2⟩ : WV I) = w := congrArg Prod.snd e
  subst e2
  exact ⟨rfl, F.en_ty g a x.2⟩

theorem big_of_le_rk (hj : X.j' < X.n) {g : Fin 2} {a : ZMod d} (h : X.n ≤ X.rkF g a) : X.big g a := by
  by_contra hb
  have := X.rk_small g a hb
  unfold RowData.rkF at h
  omega

theorem big_one_iff (a : ZMod d) : X.big 1 a ↔ ¬ X.big 0 a := by
  simpa using X.big_compl 0 a

theorem alt_odd_of_big (hdich : X.Alt ∨ ∀ a, X.big 0 a) {g : Fin 2} {a a' : ZMod d} (h1 : X.big g a)
    (h2 : X.big (1 - g) a') : X.Alt ∧ Odd (a' - a).val := by
  have h3 : ¬ X.big g a' := (X.big_compl g a').1 h2
  rcases hdich with hA | hB
  · refine ⟨hA, odd_sub_val hA.1 a a' ?_⟩
    have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp
    rcases hg with rfl | rfl
    · rw [← hA.2 a, ← hA.2 a']
      tauto
    · rw [big_one_iff] at h1 h3
      rw [← hA.2 a, ← hA.2 a']
      tauto
  · exfalso
    have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp
    rcases hg with rfl | rfl
    · exact h3 (hB a')
    · rw [big_one_iff] at h1
      exact h1 (hB a)

theorem attainsOK_of (hdich : X.Alt ∨ ∀ a, X.big 0 a) (hj : X.j' < X.n) (b : GlobalTheory d) (c : ℝ)
    (hwt : ∀ g a k, b.wt X g a k ≠ 0 → k ≤ X.rkF g a) (h : b.Attains X F c) : b.AttainsOK X F c := by
  cases b with
  | ch g a u =>
    refine ⟨(GlobalTheory.ch g a u).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, h⟩
    · intro ρ g' a1 a2 hk
      exact absurd hk (by simp [GlobalTheory.kind])
    · intro ρ _
      refine ⟨g, fun w hw => ?_⟩
      exact (vars_letter X F (MvPolynomial.vars_pow _ _ hw)).1
  | mon g e N =>
    refine ⟨(GlobalTheory.mon g e N).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, h⟩
    · intro ρ g' a1 a2 hk
      exact absurd hk (by simp [GlobalTheory.kind])
    · intro ρ _
      refine ⟨g, fun w hw => ?_⟩
      obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hw)
      exact (vars_letter X F ha).1
  | bi g a i y =>
    by_cases hy : y = 0
    · subst hy
      have hp : (GlobalTheory.bi g a i 0).poly X F = 1 := by
        simp [GlobalTheory.poly]
        rfl
      obtain ⟨S, t, ht, gr, hg, hc⟩ := h
      refine ⟨fun _ => none, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, S, t, ht, gr, hg, ?_⟩
      · intro ρ g' a1 a2 hk
        exact absurd hk (by simp)
      · intro ρ _
        refine ⟨0, fun w hw => ?_⟩
        rw [hp] at hw
        simp at hw
      · refine le_of_eq_of_le ?_ hc
        congr 1
        unfold ValOf
        rw [hp, jetAt0_one, jetAt0_one, map_prod, map_prod]
        refine Finset.prod_congr rfl fun ρ _ => ?_
        rw [map_mul, map_mul, cc_mvExp, cc_mvExp]
    · have hl : 0 < V.l ^ i * y := Nat.mul_pos (pow_pos V.l_prime.pos i) (Nat.pos_of_ne_zero hy)
      have w1 : X.n ≤ X.rkF g a := by
        apply hwt g a X.n
        simp only [GlobalTheory.wt, and_self, if_true]
        omega
      have w2 : X.n ≤ X.rkF (1 - g) (a + (i : ZMod d)) := by
        apply hwt (1 - g) (a + (i : ZMod d)) X.n
        simp only [GlobalTheory.wt, and_self, if_true]
        omega
      have hao := alt_odd_of_big X hdich (big_of_le_rk X hj w1) (big_of_le_rk X hj w2)
      refine ⟨(GlobalTheory.bi g a i y).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, h⟩
      · intro ρ g' a1 a2 hk
        have hk' : (g, a, a + (i : ZMod d)) = (g', a1, a2) := by simpa [GlobalTheory.kind] using hk
        obtain ⟨rfl, rfl, rfl⟩ : g = g' ∧ a = a1 ∧ a + (i : ZMod d) = a2 := by simpa using hk'
        refine ⟨hao.1, hao.2, fun w hw => ?_⟩
        rcases Finset.mem_union.1 (MvPolynomial.vars_mul _ _ hw) with h1 | h1
        · exact Or.inl (vars_letter X F (MvPolynomial.vars_pow _ _ h1))
        · exact Or.inr (vars_letter X F (MvPolynomial.vars_pow _ _ h1))
      · intro ρ hk
        exact absurd hk (by simp [GlobalTheory.kind])

theorem le_sum_map {α : Type} (l : List α) (f : α → ℕ) {q : α} (hq : q ∈ l) : f q ≤ (l.map f).sum := by
  induction l with
  | nil => exact absurd hq (by simp)
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hq with rfl | h
    · omega
    · have := ih h
      omega

variable {X F} in
theorem rkF_eq_of_big_iff {g g' : Fin 2} {a a' : ZMod d} (h : X.big g a ↔ X.big g' a') : X.rkF g a = X.rkF g' a' := by
  unfold RowData.rkF
  by_cases hb : X.big g a
  · rw [X.rk_big g a hb, X.rk_big g' a' (h.1 hb)]
  · rw [X.rk_small g a hb, X.rk_small g' a' (fun h' => hb (h.2 h'))]

end Formalism.L2.FormalSeriesBounds.RF

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds

section G

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)

theorem blkAdm (hdich : ∀ o ∈ Z, (X o).Alt ∨ ∀ a, (X o).big 0 a) (hj : ∀ o ∈ Z, (X o).j' < (X o).n)
    (hga : ∀ o ∈ Z, ∀ g a k, ga o g a k ≠ 0 → k ≤ (X o).rkF g a) : BlockAdmissible X F Z ga := by
  intro L hwt o ho q hq hatt
  refine attainsOK_of _ _ (hdich o ho) (hj o ho) q.1 q.2 (fun g a k hk => hga o ho g a k ?_) hatt
  rw [← hwt o ho g a k]
  have := le_sum_map (L o) (fun q => q.1.wt (X o) g a k) hq
  omega

end G

section Cc

theorem zmod_two_add_one_add_one (a : ZMod 2) : a + 1 + 1 = a := by revert a; decide

theorem zmod_two_even_succ_iff (a : ZMod 2) : Even (a + 1).val ↔ ¬ Even a.val := by revert a; decide

variable {C : Type} [Field C] {V : VF C}
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V 2 (I o) (J o)) (F : ∀ o, Flag (X o)) (gaC : Orb → ZMod 2 → ℕ → ℕ)

theorem blkAdmC (hA : ∀ o, (X o).Alt) (hj : ∀ o, (X o).j' < (X o).n)
    (hga : ∀ o s k, gaC o s k ≠ 0 → k ≤ (X o).rkF 0 s) : BlockAdmissibleSelfConjugate X F gaC := by
  intro L hwt o q hq hatt
  refine attainsOK_of _ _ (Or.inl (hA o)) (hj o) q.1 q.2 (fun g a k hk => ?_) hatt
  have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp
  rcases hg with rfl | rfl
  · apply hga o a k
    rw [← hwt o a k]
    have h : q.1.wt (X o) 0 a k + q.1.wt (X o) 1 (a + 1) k ≤ _ :=
      le_sum_map (L o) (fun q => q.1.wt (X o) 0 a k + q.1.wt (X o) 1 (a + 1) k) hq
    omega
  · have hk' : q.1.wt (X o) 1 (a + 1 + 1) k ≠ 0 := by rwa [zmod_two_add_one_add_one]
    have h1 : k ≤ (X o).rkF 0 (a + 1) := by
      apply hga o (a + 1) k
      rw [← hwt o (a + 1) k]
      have h : q.1.wt (X o) 0 (a + 1) k + q.1.wt (X o) 1 (a + 1 + 1) k ≤ _ :=
        le_sum_map (L o) (fun q => q.1.wt (X o) 0 (a + 1) k + q.1.wt (X o) 1 (a + 1 + 1) k) hq
      omega
    have h2 : (X o).big 0 (a + 1) ↔ (X o).big 1 a := by
      rw [big_one_iff, (hA o).2 (a + 1), (hA o).2 a]
      exact zmod_two_even_succ_iff a
    rwa [rkF_eq_of_big_iff h2] at h1

end Cc

end Formalism.L2.FormalSeriesBounds.RF
