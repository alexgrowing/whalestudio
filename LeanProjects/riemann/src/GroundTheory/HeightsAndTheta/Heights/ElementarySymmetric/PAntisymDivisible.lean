import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace AntisymDivisible

section General

variable {σ : Type*} [DecidableEq σ]

def collapse (u v : σ) : σ → σ := fun w => if w = u then v else w

lemma comp_collapse {u v : σ} (x : σ → ℝ) (hx : x u = x v) : x ∘ collapse u v = x := by
  funext w
  simp only [Function.comp, collapse]
  split_ifs with h
  · subst h; exact hx.symm
  · rfl

lemma sub_rename_collapse_mem (u v : σ) (P : MvPolynomial σ ℝ) :
    P - rename (collapse u v) P ∈ Ideal.span {(X u - X v : MvPolynomial σ ℝ)} := by
  set I := Ideal.span {(X u - X v : MvPolynomial σ ℝ)}
  have h : (Ideal.Quotient.mkₐ ℝ I).comp (rename (collapse u v)) = Ideal.Quotient.mkₐ ℝ I := by
    refine MvPolynomial.algHom_ext fun w => ?_
    simp only [AlgHom.comp_apply, rename_X, collapse, Ideal.Quotient.mkₐ_eq_mk]
    split_ifs with hw
    · subst hw
      exact (Ideal.Quotient.eq.2 (Ideal.subset_span (Set.mem_singleton _))).symm
    · rfl
  rw [← Ideal.Quotient.eq]
  have := congrArg (fun f => f P) h
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
  exact this.symm

lemma dvd_of_vanish (u v : σ) (P : MvPolynomial σ ℝ)
    (h : ∀ x : σ → ℝ, x u = x v → eval x P = 0) : (X u - X v) ∣ P := by
  have h0 : rename (collapse u v) P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [eval_rename, map_zero]
    apply h
    simp only [Function.comp, collapse, if_pos rfl]
    split_ifs <;> rfl
  have := sub_rename_collapse_mem u v P
  rw [h0, sub_zero] at this
  exact Ideal.mem_span_singleton.1 this

lemma prime_X_sub_X {u v : σ} (huv : u ≠ v) : Prime (X u - X v : MvPolynomial σ ℝ) := by
  have hne : (X u - X v : MvPolynomial σ ℝ) ≠ 0 := by
    rw [sub_ne_zero]; exact fun h => huv (X_injective h)
  rw [← Ideal.span_singleton_prime hne]
  have : Ideal.span {(X u - X v : MvPolynomial σ ℝ)} =
      RingHom.ker (rename (R := ℝ) (collapse u v)) := by
    ext P
    constructor
    · intro hP
      obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton.1 hP
      rw [RingHom.mem_ker]
      simp [collapse]
    · intro hP
      rw [RingHom.mem_ker] at hP
      have := sub_rename_collapse_mem u v P
      rwa [hP, sub_zero] at this
  rw [this]
  exact RingHom.ker_isPrime _

lemma pair_of_dvd {u v u' v' : σ} (h' : u' ≠ v')
    (hd : (X u - X v : MvPolynomial σ ℝ) ∣ X u' - X v') :
    (u' = u ∧ v' = v) ∨ (u' = v ∧ v' = u) := by
  obtain ⟨Q, hQ⟩ := hd
  have h1 := congrArg (rename (R := ℝ) (collapse u v)) hQ
  simp only [map_sub, map_mul, rename_X, collapse, ↓reduceIte, ite_self, sub_self, zero_mul,
    sub_eq_zero] at h1
  have h2 := X_injective h1
  split_ifs at h2 with ha hb hb
  · exact absurd (ha.trans hb.symm) h'
  · exact Or.inl ⟨ha, h2.symm⟩
  · exact Or.inr ⟨h2, hb⟩
  · exact absurd h2 h'

lemma vanish_of_swap (u v : σ) (P : MvPolynomial σ ℝ) (h : rename (Equiv.swap u v) P = -P) :
    ∀ x : σ → ℝ, x u = x v → eval x P = 0 := by
  intro x hx
  have e : x ∘ ⇑(Equiv.swap u v) = x := by
    funext w
    simp only [Function.comp]
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, hx]
    · rw [h2, hx]
    · rfl
  have := congrArg (eval x) h
  rw [eval_rename, e, map_neg] at this
  linarith

lemma vanish_of_open [Fintype σ] (u v : σ) (P : MvPolynomial σ ℝ) (O : Set (σ → ℝ))
    (hO : IsOpen O) (hne : (O ∩ {x | x u = x v}).Nonempty)
    (h : ∀ x ∈ O ∩ {x | x u = x v}, eval x P = 0) :
    ∀ x : σ → ℝ, x u = x v → eval x P = 0 := by
  obtain ⟨x0, hx0O, hx0H⟩ := hne
  have hx0H' : x0 u = x0 v := hx0H
  have hQ : rename (collapse u v) P = 0 := by
    have hO' : IsOpen {y : σ → ℝ | y ∘ collapse u v ∈ O} :=
      hO.preimage (continuous_pi fun w => continuous_apply (collapse u v w))
    have hx0 : x0 ∈ {y : σ → ℝ | y ∘ collapse u v ∈ O} := by
      show x0 ∘ collapse u v ∈ O
      rwa [comp_collapse x0 hx0H']
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO' x0 hx0
    rw [ball_pi x0 hε] at hball
    refine MvPolynomial.funext_set (fun w => Metric.ball (x0 w) ε) (fun w => ?_) fun y hy => ?_
    · rw [Real.ball_eq_Ioo]
      exact Set.Ioo_infinite (by linarith)
    · rw [eval_rename, map_zero]
      apply h
      refine ⟨hball hy, ?_⟩
      show (y ∘ collapse u v) u = (y ∘ collapse u v) v
      simp only [Function.comp, collapse, if_pos rfl]
      split_ifs <;> rfl
  intro x hx
  have := congrArg (eval x) hQ
  rwa [eval_rename, comp_collapse x hx, map_zero] at this

lemma prod_dvd_of_primes {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ)
    (P : MvPolynomial σ ℝ) (hp : ∀ i ∈ s, Prime (f i))
    (hnd : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → ¬ f i ∣ f k) (hd : ∀ i ∈ s, f i ∣ P) :
    ∏ i ∈ s, f i ∣ P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    obtain ⟨Q, hQ⟩ := ih (fun k hk => hp k (Finset.mem_insert_of_mem hk))
      (fun a ha b hb hab => hnd a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab)
      (fun k hk => hd k (Finset.mem_insert_of_mem hk))
    have hpi := hp i (Finset.mem_insert_self i s)
    have hiP := hd i (Finset.mem_insert_self i s)
    rw [hQ] at hiP
    rcases hpi.dvd_or_dvd hiP with h | h
    · exfalso
      obtain ⟨k, hk, hik⟩ := (hpi.dvd_finsetProd_iff f).1 h
      exact hnd i (Finset.mem_insert_self i s) k (Finset.mem_insert_of_mem hk)
        (by rintro rfl; exact hi hk) hik
    · obtain ⟨R, rfl⟩ := h
      exact ⟨R, by rw [hQ]; ring⟩

lemma homogeneousComponent_mul_of_isHomogeneous {Δ : MvPolynomial σ ℝ} {D : ℕ}
    (hΔ : Δ.IsHomogeneous D) (l : MvPolynomial σ ℝ) (n : ℕ) :
    homogeneousComponent (D + n) (Δ * l) = Δ * homogeneousComponent n l := by
  conv_lhs => rw [← sum_homogeneousComponent l]
  rw [Finset.mul_sum, map_sum]
  have key : ∀ m, homogeneousComponent (D + n) (Δ * homogeneousComponent m l) =
      if n = m then Δ * homogeneousComponent n l else 0 := by
    intro m
    rw [homogeneousComponent_of_mem (hΔ.mul (homogeneousComponent_isHomogeneous m l))]
    by_cases h : n = m
    · subst h; simp
    · rw [if_neg (by omega), if_neg h]
  simp_rw [key]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero, mul_zero]
    simp only [Finset.mem_range, not_lt] at h
    omega

end General

section Blocks

lemma block_chain {N j : ℕ} (R : Fin N → Fin N → Prop)
    (hadj : ∀ a b : Fin N, b.val = a.val + 1 → (b.val < j ∨ j ≤ a.val) → R a b)
    (hstep : ∀ a c b : Fin N, a.val < c.val → c.val + 1 = b.val → (b.val < j ∨ j ≤ a.val) →
      R a c → R c b → R a b) :
    ∀ a b : Fin N, a.val < b.val → (b.val < j ∨ j ≤ a.val) → R a b := by
  suffices H : ∀ k : ℕ, ∀ a b : Fin N, b.val = a.val + 1 + k → (b.val < j ∨ j ≤ a.val) → R a b by
    intro a b hab hbl
    exact H (b.val - a.val - 1) a b (by omega) hbl
  intro k
  induction k with
  | zero => intro a b hb hbl; exact hadj a b (by omega) hbl
  | succ k ih =>
    intro a b hb hbl
    have hcN : a.val + 1 + k < N := by omega
    let c : Fin N := ⟨a.val + 1 + k, hcN⟩
    exact hstep a c b (by simp only [c]; omega) (by simp only [c]; omega) hbl
      (ih a c rfl (by simp only [c]; omega)) (hadj c b (by simp only [c]; omega) (by simp only [c]; omega))

variable {T : Type} [Fintype T] [DecidableEq T] {N : ℕ}

lemma swap_pair (τ : T) (a b i : Fin N) :
    Equiv.swap (τ, a) (τ, b) (τ, i) = (τ, Equiv.swap a b i) := by
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  split_ifs <;> simp_all

lemma delta_factor_eq_det (τ : T) :
    ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, (X (τ, a) - X (τ, b) : MvPolynomial (T × Fin N) ℝ) =
      (Matrix.vandermonde (fun i : Fin N => (-X (τ, i) : MvPolynomial (T × Fin N) ℝ))).det := by
  rw [Matrix.det_vandermonde]
  simp only [neg_sub_neg]

lemma rename_swap_delta (τ₀ : T) {a b : Fin N} (hab : a ≠ b) :
    rename (Equiv.swap (τ₀, a) (τ₀, b)) (antisymDelta T N) = -antisymDelta T N := by
  have key : ∀ τ, rename (R := ℝ) (Equiv.swap (τ₀, a) (τ₀, b))
      (Matrix.vandermonde (fun i : Fin N => (-X (τ, i) : MvPolynomial (T × Fin N) ℝ))).det =
      (if τ = τ₀ then -1 else 1) *
        (Matrix.vandermonde (fun i : Fin N => (-X (τ, i) : MvPolynomial (T × Fin N) ℝ))).det := by
    intro τ
    rw [AlgHom.map_det]
    by_cases hτ : τ = τ₀
    · subst hτ
      have : (rename (R := ℝ) (Equiv.swap (τ, a) (τ, b))).mapMatrix
          (Matrix.vandermonde (fun i : Fin N => (-X (τ, i) : MvPolynomial (T × Fin N) ℝ))) =
          (Matrix.vandermonde (fun i : Fin N => (-X (τ, i) : MvPolynomial (T × Fin N) ℝ))).submatrix
            (Equiv.swap a b) id := by
        ext i k
        simp [Matrix.vandermonde_apply, swap_pair]
      rw [this, Matrix.det_permute, Equiv.Perm.sign_swap hab]
      simp
    · have : (rename (R := ℝ) (Equiv.swap (τ₀, a) (τ₀, b))).mapMatrix
          (Matrix.vandermonde (fun i : Fin N => (-X (τ, i) : MvPolynomial (T × Fin N) ℝ))) =
          Matrix.vandermonde (fun i : Fin N => (-X (τ, i) : MvPolynomial (T × Fin N) ℝ)) := by
        ext i k
        simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.vandermonde_apply, map_pow,
          map_neg, rename_X]
        rw [Equiv.swap_apply_of_ne_of_ne (by simp [hτ]) (by simp [hτ])]
      rw [this, if_neg hτ, one_mul]
  unfold antisymDelta
  simp_rw [delta_factor_eq_det]
  rw [map_prod]
  simp_rw [key]
  rw [Finset.prod_mul_distrib]
  simp [Finset.prod_ite_eq']

lemma isHomogeneous_delta : (antisymDelta T N).IsHomogeneous (antisymDegree T N) := by
  have h : (antisymDelta T N).IsHomogeneous (∑ τ : T, ∑ a : Fin N, ∑ b ∈ Finset.Ioi a, 1) := by
    unfold antisymDelta
    refine IsHomogeneous.prod _ _ _ fun τ _ => IsHomogeneous.prod _ _ _ fun a _ =>
      IsHomogeneous.prod _ _ _ fun b _ => ?_
    exact (isHomogeneous_X ℝ _).sub (isHomogeneous_X ℝ _)
  have e : (∑ τ : T, ∑ a : Fin N, ∑ b ∈ Finset.Ioi a, 1) = antisymDegree T N := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, antisymDegree]
    congr 1
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Ioi]
    rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N, Finset.sum_range_reflect (fun i => i) N,
      Finset.sum_range_id, Nat.choose_two_right]
  rwa [e] at h

end Blocks

end AntisymDivisible

open AntisymDivisible in

theorem AntisymDivisible.proof : AntisymDivisible.Statement := by
  intro T _ _ N j P hP hvan
  obtain ⟨hPh, hPa⟩ := hP

  have anti : ∀ (τ : T) (a b : Fin N), a.val < b.val → (b.val < j ∨ j ≤ a.val) →
      rename (Equiv.swap (τ, a) (τ, b)) P = -P := by
    intro τ
    refine block_chain (fun a b => rename (Equiv.swap (τ, a) (τ, b)) P = -P) ?_ ?_
    · intro a b hb hbl
      exact hPa _ ⟨τ, a, b, hb, hbl, rfl⟩
    · intro a c b hac hcb hbl h1 h2
      have hca : (τ, a) ≠ (τ, c) := by simp [Fin.ext_iff]; omega
      have hba : (τ, a) ≠ (τ, b) := by simp [Fin.ext_iff]; omega
      have e := Equiv.swap_apply_apply (Equiv.swap (τ, c) (τ, b)) (τ, a) (τ, c)
      rw [Equiv.swap_apply_of_ne_of_ne hca hba, Equiv.swap_apply_left, Equiv.swap_inv] at e
      rw [e, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, ← rename_rename, ← rename_rename,
        h2, map_neg, h1, neg_neg, h2]

  set S : Finset (T × Fin N × Fin N) := Finset.univ.filter (fun t => t.2.1 < t.2.2) with hS
  let f : T × Fin N × Fin N → MvPolynomial (T × Fin N) ℝ := fun t => X (t.1, t.2.1) - X (t.1, t.2.2)
  have hΔ : antisymDelta T N = ∏ t ∈ S, f t := by
    simp only [antisymDelta, S, f, Finset.prod_filter, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun a _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext b
    simp
  have hprime : ∀ t ∈ S, Prime (f t) := by
    intro t ht
    simp only [S, Finset.mem_filter] at ht
    exact prime_X_sub_X (by simp [Fin.ext_iff]; omega)
  have hΔdvd : antisymDelta T N ∣ P := by
    rw [hΔ]
    refine prod_dvd_of_primes S f P hprime ?_ ?_
    · rintro ⟨τ, a, b⟩ ht ⟨τ', a', b'⟩ ht' hne hdv
      simp only [S, Finset.mem_filter] at ht ht'
      rcases pair_of_dvd (by simp [Fin.ext_iff]; omega) hdv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [Prod.mk.injEq] at h1 h2
        exact hne (by rw [h1.1, h1.2, h2.2])
      · simp only [Prod.mk.injEq] at h1 h2
        rw [h1.2, h2.2] at ht'
        exact absurd (ht.2.trans ht'.2) (lt_irrefl _)
    · rintro ⟨τ, a, b⟩ ht
      simp only [S, Finset.mem_filter] at ht
      apply dvd_of_vanish
      by_cases hc : a.val < j ∧ j ≤ b.val
      · obtain ⟨O, hO, hne, h0⟩ := hvan τ a b hc.1 hc.2
        exact vanish_of_open _ _ P O hO hne h0
      · exact vanish_of_swap _ _ P (anti τ a b ht.2 (by omega))
  obtain ⟨l, hl⟩ := hΔdvd

  have hΔh := isHomogeneous_delta (T := T) (N := N)
  have hP1 : P = antisymDelta T N * homogeneousComponent 1 l := by
    have := homogeneousComponent_mul_of_isHomogeneous hΔh l 1
    rw [← hl, homogeneousComponent_of_mem hPh, if_pos rfl] at this
    exact this
  have hΔ0 : antisymDelta T N ≠ 0 := by
    rw [hΔ, Finset.prod_ne_zero_iff]
    exact fun t ht => (hprime t ht).ne_zero
  set l₁ := homogeneousComponent 1 l with hl₁
  have hl₁h : l₁ ∈ homogeneousSubmodule (T × Fin N) ℝ 1 := homogeneousComponent_isHomogeneous 1 l

  have inv : ∀ (τ : T) (a b : Fin N), a.val < b.val → (b.val < j ∨ j ≤ a.val) →
      rename (Equiv.swap (τ, a) (τ, b)) l₁ = l₁ := by
    intro τ a b hab hbl
    have h1 := anti τ a b hab hbl
    have h2 := rename_swap_delta (T := T) τ (ne_of_lt hab)
    rw [hP1, map_mul, h2] at h1
    apply mul_left_cancel₀ hΔ0
    linear_combination -h1

  rw [homogeneousSubmodule_one_eq_span_X, Submodule.mem_span_range_iff_exists_fun] at hl₁h
  obtain ⟨c, hc⟩ := hl₁h
  have coeff_lin : ∀ (g : T × Fin N → T × Fin N) (u : T × Fin N),
      coeff (Finsupp.single u 1) (∑ w, c w • (X (g w) : MvPolynomial (T × Fin N) ℝ)) =
        ∑ w, if g w = u then c w else 0 := by
    intro g u
    simp only [coeff_sum, coeff_smul, coeff_X, Finsupp.single_left_inj one_ne_zero, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
  have const : ∀ (τ : T) (a b : Fin N), a.val < b.val → (b.val < j ∨ j ≤ a.val) →
      c (τ, a) = c (τ, b) := by
    intro τ a b hab hbl
    have h := congrArg (coeff (Finsupp.single (τ, a) 1)) (inv τ a b hab hbl)
    rw [← hc, map_sum] at h
    simp only [map_smul, rename_X] at h
    rw [coeff_lin, coeff_lin] at h
    simp only [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, id] at h
    exact h.symm
  refine ⟨l₁, ⟨?_, ?_⟩, hP1⟩
  · exact homogeneousComponent_isHomogeneous 1 l
  · intro g hg
    rw [← hc, map_sum]
    simp only [map_smul, rename_X]
    have hcg : ∀ w, c (g w) = c w := by
      rintro ⟨τ, a⟩
      obtain ⟨h1, h2⟩ := hg (τ, a)
      rcases hga : g (τ, a) with ⟨τ', a'⟩
      rw [hga] at h1 h2
      simp only at h1 h2
      subst h1
      rcases lt_trichotomy a.val a'.val with h | h | h
      · refine (const τ' a a' h ?_).symm
        by_cases ha : a.val < j
        · exact Or.inl (h2.2 ha)
        · exact Or.inr (by omega)
      · rw [Fin.ext h]
      · refine const τ' a' a h ?_
        by_cases ha : a.val < j
        · exact Or.inl ha
        · exact Or.inr (by have := mt h2.1 ha; omega)
    calc ∑ w, c w • X (g w) = ∑ w, c (g w) • (X (g w) : MvPolynomial (T × Fin N) ℝ) := by
          simp_rw [hcg]
      _ = ∑ w, c w • X w := Equiv.sum_comp g (fun w => c w • (X w : MvPolynomial (T × Fin N) ℝ))

end GroundTheory.Heights₂.Heights
