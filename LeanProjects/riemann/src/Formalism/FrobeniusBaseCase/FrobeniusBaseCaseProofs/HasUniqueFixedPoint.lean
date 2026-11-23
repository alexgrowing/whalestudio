import Formalism.FrobeniusBaseCase.Statement

open MvPowerSeries

namespace Formalism.BaseCaseIdentities

noncomputable section

open Classical

variable {k : Type*} [Field k] {Z : Type*} {C : Type*}

theorem OrdGE.mono {a b : ℕ} {f : MvPowerSeries Z k} (h : a ≤ b) (hf : OrdGE b f) : OrdGE a f := by
  intro A hA
  exact hf A (lt_of_lt_of_le hA h)

theorem OrdGE.zero {n : ℕ} : OrdGE n (0 : MvPowerSeries Z k) := by
  intro A _
  simp

theorem OrdGE.add {n : ℕ} {f g : MvPowerSeries Z k} (hf : OrdGE n f) (hg : OrdGE n g) :
    OrdGE n (f + g) := by
  intro A hA
  rw [map_add, hf A hA, hg A hA, add_zero]

theorem OrdGE.neg {n : ℕ} {f : MvPowerSeries Z k} (hf : OrdGE n f) : OrdGE n (-f) := by
  intro A hA
  rw [map_neg, hf A hA, neg_zero]

theorem OrdGE.sub {n : ℕ} {f g : MvPowerSeries Z k} (hf : OrdGE n f) (hg : OrdGE n g) :
    OrdGE n (f - g) := by
  intro A hA
  rw [map_sub, hf A hA, hg A hA, sub_zero]

theorem OrdGE.sum {ι : Type*} {n : ℕ} (s : Finset ι) {f : ι → MvPowerSeries Z k}
    (hf : ∀ i ∈ s, OrdGE n (f i)) : OrdGE n (∑ i ∈ s, f i) := by
  intro A hA
  rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => hf i hi A hA

theorem OrdGE.mul {a b : ℕ} {f g : MvPowerSeries Z k} (hf : OrdGE a f) (hg : OrdGE b g) :
    OrdGE (a + b) (f * g) := by
  intro A hA
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' : p.1 + p.2 = A := by simpa using hp
  have hd : p.1.degree + p.2.degree = A.degree := by
    rw [← hp', map_add]
  by_cases h1 : p.1.degree < a
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]

theorem OrdGE.C_mul {n : ℕ} {f : MvPowerSeries Z k} (x : k) (hf : OrdGE n f) :
    OrdGE n (MvPowerSeries.C x * f) := by
  intro A hA
  rw [coeff_C_mul, hf A hA, mul_zero]

theorem OrdGE.pow {f : MvPowerSeries Z k} (hf : OrdGE 1 f) (n : ℕ) : OrdGE n (f ^ n) := by
  induction n with
  | zero => intro A hA; exact absurd hA (Nat.not_lt_zero _)
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem OrdGE.X (d : Z) : OrdGE 1 (X d : MvPowerSeries Z k) := by
  intro A hA
  rw [coeff_X]
  split_ifs with h
  · subst h
    simp at hA
  · rfl

theorem OrdGE.pow_sub_pow {f g : MvPowerSeries Z k} {n : ℕ} (hf : OrdGE 1 f) (hg : OrdGE 1 g)
    (hfg : OrdGE (n + 1) (f - g)) {N : ℕ} (hN : 1 ≤ N) : OrdGE (n + N) (f ^ N - g ^ N) := by
  rw [← geom_sum₂_mul]
  have hs : OrdGE (N - 1) (∑ i ∈ Finset.range N, f ^ i * g ^ (N - 1 - i)) := by
    refine OrdGE.sum _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact OrdGE.mono (show N - 1 ≤ i + (N - 1 - i) by omega) ((hf.pow i).mul (hg.pow (N - 1 - i)))
  exact OrdGE.mono (by omega) (hs.mul hfg)

theorem eq_of_ordGE {f g : MvPowerSeries Z k} (h : ∀ n : ℕ, OrdGE (n + 1) (f - g)) : f = g := by
  ext A
  have h0 := h A.degree A (Nat.lt_succ_self _)
  rw [map_sub, sub_eq_zero] at h0
  exact h0

theorem frobeniusSubstSpec (k : Type*) [Field k] (Z : Type*) : FrobSpec k Z := by
  intro N f hN
  constructor
  · intro A
    have hA : (N • A).mapRange (· / N) (Nat.zero_div N) = A := by
      ext d
      rw [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul,
        Nat.mul_div_cancel_left _ (by omega : 0 < N)]
    show frob N f (N • A) = _
    unfold frob
    rw [if_pos (fun d => by rw [Finsupp.smul_apply, smul_eq_mul]; exact Nat.dvd_mul_right _ _), hA]
  · intro B hB
    show frob N f B = 0
    unfold frob
    rw [if_neg]
    intro hdiv
    apply hB
    refine ⟨B.mapRange (· / N) (Nat.zero_div N), ?_⟩
    ext d
    rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply, Nat.mul_div_cancel' (hdiv d)]

namespace Data

variable [Fintype Z] [Fintype C] (D : Data k Z C)

theorem coeff_Psi (t : C → MvPowerSeries Z k) (b : C) (A : Z →₀ ℕ) :
    coeff A (D.Psi t b) = coeff A (D.zvec b) -
      ∑ c, ∑ j ∈ Finset.Icc 1 A.degree, D.al c j b * coeff A (t c ^ (D.l ^ j)) := rfl

theorem coeff_PsiPartial (N : ℕ) (t : C → MvPowerSeries Z k) (b : C) (A : Z →₀ ℕ) :
    coeff A (D.PsiPartial N t b) = coeff A (D.zvec b) -
      ∑ c, ∑ j ∈ Finset.Icc 1 N, D.al c j b * coeff A (t c ^ (D.l ^ j)) := by
  simp only [PsiPartial, map_sub, map_sum, coeff_C_mul]

theorem noConst_zvec : NoConst D.zvec := by
  intro b
  refine OrdGE.sum _ fun d _ => ?_
  split_ifs
  · exact OrdGE.X d
  · exact OrdGE.zero

theorem one_lt_l : 1 < D.l := by
  have := D.l_ge
  omega

theorem opIsLimit : D.PsiIsLimit := by
  intro t ht b A N hN
  rw [coeff_Psi, coeff_PsiPartial]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hN) fun j hj hj' => ?_
  rw [Finset.mem_Icc] at hj hj'
  have hlt : A.degree < D.l ^ j := by
    have h1 : j < D.l ^ j := Nat.lt_pow_self D.one_lt_l
    omega
  rw [(ht c).pow (D.l ^ j) A hlt, mul_zero]

theorem noConst_Psi (t : C → MvPowerSeries Z k) : NoConst (D.Psi t) := by
  intro b A hA
  have h0 : A.degree = 0 := by omega
  rw [coeff_Psi, h0, D.noConst_zvec b A hA]
  simp

theorem contracts : D.Contraction := by
  intro t t' n ht ht' h b A hA
  rw [map_sub, coeff_Psi, coeff_Psi, sub_eq_zero]
  congr 1
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  have hl : D.l ≤ D.l ^ j := Nat.le_self_pow (by omega) _
  have hN : 1 ≤ D.l ^ j := Nat.one_le_pow _ _ (by have := D.one_lt_l; omega)
  have hc := OrdGE.pow_sub_pow (ht c) (ht' c) (h c) hN A (by omega)
  rw [map_sub, sub_eq_zero] at hc
  rw [hc]

theorem noConst_iterate {t : C → MvPowerSeries Z k} (ht : NoConst t) (n : ℕ) :
    NoConst ((D.Psi)^[n] t) := by
  cases n with
  | zero => exact ht
  | succ n => rw [Function.iterate_succ_apply']; exact D.noConst_Psi _

theorem iterate_close {a b : C → MvPowerSeries Z k} (ha : NoConst a) (hb : NoConst b) (n : ℕ) :
    ∀ c, OrdGE (n + 1) ((D.Psi)^[n] a c - (D.Psi)^[n] b c) := by
  induction n with
  | zero => intro c; exact (ha c).sub (hb c)
  | succ n ih =>
    intro c
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h := D.contracts _ _ n (D.noConst_iterate ha n) (D.noConst_iterate hb n) ih c
    have := D.l_ge
    exact OrdGE.mono (by omega) h

def fixPt : C → MvPowerSeries Z k := fun c A => coeff A ((D.Psi)^[A.degree] 0 c)

theorem noConst_zero : NoConst (0 : C → MvPowerSeries Z k) := by
  intro c A _
  simp

theorem coeff_iterate_zero (c : C) (A : Z →₀ ℕ) {n : ℕ} (hn : A.degree ≤ n) :
    coeff A ((D.Psi)^[n] 0 c) = coeff A (D.fixPt c) := by
  have e : coeff A (D.fixPt c) = coeff A ((D.Psi)^[A.degree] 0 c) := rfl
  rw [e]
  have hn' : n = A.degree + (n - A.degree) := by omega
  rw [hn', Function.iterate_add_apply]
  have h := D.iterate_close (D.noConst_iterate noConst_zero (n - A.degree)) noConst_zero
    A.degree c A (Nat.lt_succ_self _)
  rw [map_sub, sub_eq_zero] at h
  exact h

theorem fixPt_close (n : ℕ) (c : C) : OrdGE (n + 1) (D.fixPt c - (D.Psi)^[n] 0 c) := by
  intro A hA
  rw [map_sub, D.coeff_iterate_zero c A (by omega), sub_self]

theorem noConst_fixPt : NoConst D.fixPt := by
  intro c A hA
  exact D.noConst_iterate noConst_zero A.degree c A hA

theorem Psi_fixPt : D.Psi D.fixPt = D.fixPt := by
  funext b
  ext A
  have h := D.contracts D.fixPt ((D.Psi)^[A.degree] 0) A.degree D.noConst_fixPt
    (D.noConst_iterate noConst_zero _) (fun c => D.fixPt_close A.degree c) b A
    (by have := D.one_lt_l; omega)
  rw [map_sub, sub_eq_zero, ← Function.iterate_succ_apply' D.Psi] at h
  rw [h, D.coeff_iterate_zero b A (Nat.le_succ _)]

theorem hasUniqueFixedPoint : D.FixedPoint := by
  refine ⟨⟨D.fixPt, ⟨D.noConst_fixPt, D.Psi_fixPt⟩, ?_⟩, ?_⟩
  · rintro y ⟨hy, hy'⟩
    funext c
    apply eq_of_ordGE
    intro n
    have h := D.iterate_close hy D.noConst_fixPt n c
    rwa [Function.iterate_fixed hy', Function.iterate_fixed D.Psi_fixPt] at h
  · intro t0 t ht0 ht hfix n A hA c
    have h := D.iterate_close ht0 ht n c A (by omega)
    rw [map_sub, sub_eq_zero, Function.iterate_fixed hfix] at h
    exact h

end Data

end

end Formalism.BaseCaseIdentities
