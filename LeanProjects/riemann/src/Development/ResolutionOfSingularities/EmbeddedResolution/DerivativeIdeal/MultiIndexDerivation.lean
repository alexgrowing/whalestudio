import Mathlib

namespace FunctorialResolution.EmbeddedResolution

section

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

def multiIndexDeriv {h : ℕ} (D : Fin h → Derivation k R R) (α : Fin h → ℕ) (x : R) : R :=
  Fin.foldr h (fun i y => (⇑(D i))^[α i] y) x

@[simp]
theorem multiIndexDeriv_of_isEmpty (D : Fin 0 → Derivation k R R) (α : Fin 0 → ℕ) :
    multiIndexDeriv D α = id := by
  funext x
  simp [multiIndexDeriv]

private theorem foldr_eq_self_of_forall_eq_self {A : Type*} :
    ∀ (n : ℕ) (f : Fin n → A → A), (∀ (i : Fin n) (y : A), f i y = y) →
      ∀ x : A, Fin.foldr n f x = x := by
  intro n
  induction n with
  | zero =>
      intro f hf x
      simp
  | succ n ih =>
      intro f hf x
      rw [Fin.foldr_succ, ih (fun i => f i.succ) (fun i y => hf i.succ y) x]
      exact hf 0 x

@[simp]
theorem multiIndexDeriv_zero {h : ℕ} (D : Fin h → Derivation k R R) (f : R) :
    multiIndexDeriv D (0 : Fin h → ℕ) f = f := by
  unfold multiIndexDeriv
  exact foldr_eq_self_of_forall_eq_self h (fun i y => (⇑(D i))^[(0 : Fin h → ℕ) i] y)
    (fun i y => by simp) f

@[simp]
theorem multiIndexDeriv_fun_zero {h : ℕ} (D : Fin h → Derivation k R R) (f : R) :
    multiIndexDeriv D (fun _ => 0) f = f :=
  multiIndexDeriv_zero D f

private theorem mul_pow_sub_one_le (J : Ideal R) (n : ℕ) :
    J * J ^ (n - 1) ≤ J ^ n := by
  cases n with
  | zero =>
      show J * J ^ 0 ≤ J ^ 0
      rw [pow_zero, Ideal.one_eq_top]
      exact le_top
  | succ m =>
      show J * J ^ m ≤ J ^ (m + 1)
      exact le_of_eq (by rw [mul_comm, ← pow_succ])

private theorem derivation_mem_pow_sub_one (J : Ideal R) (D : Derivation k R R) :
    ∀ (n : ℕ) (f : R), f ∈ J ^ n → D f ∈ J ^ (n - 1) := by
  intro n
  induction n with
  | zero =>
      intro f _
      show D f ∈ J ^ 0
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  | succ m ih =>
      intro f hf
      rw [pow_succ] at hf
      show D f ∈ J ^ m
      refine Submodule.mul_induction_on (C := fun x => D x ∈ J ^ m) hf ?_ ?_
      · intro a ha b hb
        have hDa : D a ∈ J ^ (m - 1) := ih a ha
        have hL : D (a * b) = a * D b + b * D a := by
          rw [D.leibniz, smul_eq_mul, smul_eq_mul]
        show D (a * b) ∈ J ^ m
        rw [hL]
        refine Submodule.add_mem _ (Ideal.mul_mem_right _ _ ha) ?_
        exact mul_pow_sub_one_le J m (Ideal.mul_mem_mul hb hDa)
      · intro x y hx hy
        show D (x + y) ∈ J ^ m
        rw [map_add]
        exact Submodule.add_mem _ hx hy

private theorem iterate_derivation_mem_pow_sub (J : Ideal R) (D : Derivation k R R) :
    ∀ (m n : ℕ) (f : R), f ∈ J ^ n → (⇑D)^[m] f ∈ J ^ (n - m) := by
  intro m
  induction m with
  | zero =>
      intro n f hf
      rw [Function.iterate_zero_apply, Nat.sub_zero]
      exact hf
  | succ m ih =>
      intro n f hf
      rw [Function.iterate_succ_apply]
      have h1 : D f ∈ J ^ (n - 1) := derivation_mem_pow_sub_one J D n f hf
      have h2 := ih (n - 1) (D f) h1
      have h3 : n - 1 - m = n - (m + 1) := by omega
      rw [h3] at h2
      exact h2

private theorem foldr_iterate_mem_pow_sub (J : Ideal R) :
    ∀ (h : ℕ) (D : Fin h → Derivation k R R) (α : Fin h → ℕ) (n : ℕ) (f : R), f ∈ J ^ n →
      Fin.foldr h (fun i y => (⇑(D i))^[α i] y) f ∈ J ^ (n - ∑ i, α i) := by
  intro h
  induction h with
  | zero =>
      intro D α n f hf
      have hz : ∑ i : Fin 0, α i = 0 := by simp
      rw [Fin.foldr_zero, hz, Nat.sub_zero]
      exact hf
  | succ h ih =>
      intro D α n f hf
      have hinner : Fin.foldr h (fun i y => (⇑(D i.succ))^[α i.succ] y) f
          ∈ J ^ (n - ∑ i : Fin h, α i.succ) :=
        ih (fun i => D i.succ) (fun i => α i.succ) n f hf
      have h2 := iterate_derivation_mem_pow_sub J (D 0) (α 0)
        (n - ∑ i : Fin h, α i.succ) _ hinner
      have hs0 : ∑ i, α i = α 0 + ∑ i : Fin h, α i.succ := Fin.sum_univ_succ α
      have hs : n - ∑ i, α i = n - (∑ i : Fin h, α i.succ) - α 0 := by
        rw [hs0]; omega
      rw [Fin.foldr_succ, hs]
      exact h2

theorem multiIndexDeriv_mem_pow_sub {h : ℕ} (D : Fin h → Derivation k R R) (J : Ideal R) (n : ℕ)
    {f : R} (hf : f ∈ J ^ n) (α : Fin h → ℕ) :
    multiIndexDeriv D α f ∈ J ^ (n - ∑ i, α i) := by
  exact foldr_iterate_mem_pow_sub J h D α n f hf

private theorem derivation_natCast_mul {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    (D : Derivation B S S) (m : ℕ) (x : S) : D ((m : S) * x) = (m : S) * D x := by
  have h1 : ((m : S) * x) = m • x := by rw [nsmul_eq_mul]
  have h2 : ((m : S) * D x) = m • D x := by rw [nsmul_eq_mul]
  rw [h1, h2, map_nsmul]

private theorem iterate_derivation_natCast_mul {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    (D : Derivation B S S) (m c : ℕ) (x : S) :
    (⇑D)^[m] ((c : S) * x) = (c : S) * (⇑D)^[m] x := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, derivation_natCast_mul]

private theorem iterate_derivation_sum {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    (D : Derivation B S S) (m : ℕ) {ι : Type*} (s : Finset ι) (F : ι → S) :
    (⇑D)^[m] (∑ i ∈ s, F i) = ∑ i ∈ s, (⇑D)^[m] (F i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, map_sum]

private theorem sum_choose_succ_mul_eq {S : Type*} [CommRing S] (u v : ℕ → S) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : S) * (u (i + 1) * v (n - i)))
        + (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : S) * (u i * v (n + 1 - i)))
      = ∑ i ∈ Finset.range (n + 1 + 1), (((n + 1).choose i : ℕ) : S) * (u i * v (n + 1 - i)) := by
  have e1 : (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : S) * (u (i + 1) * v (n - i)))
      = (∑ i ∈ Finset.range n, ((n.choose i : ℕ) : S) * (u (i + 1) * v (n - i)))
        + u (n + 1) * v 0 := by
    rw [Finset.sum_range_succ]
    simp
  have e2 : (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : S) * (u i * v (n + 1 - i)))
      = (∑ i ∈ Finset.range n, ((n.choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
        + u 0 * v (n + 1) := by
    rw [Finset.sum_range_succ']
    simp
  have e3 : (∑ i ∈ Finset.range (n + 1 + 1), (((n + 1).choose i : ℕ) : S) * (u i * v (n + 1 - i)))
      = (∑ i ∈ Finset.range (n + 1), (((n + 1).choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
        + u 0 * v (n + 1) := by
    rw [Finset.sum_range_succ']
    simp
  have e4 : (∑ i ∈ Finset.range (n + 1),
        (((n + 1).choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
      = (∑ i ∈ Finset.range n, (((n + 1).choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
        + u (n + 1) * v 0 := by
    rw [Finset.sum_range_succ]
    simp
  have e5 : (∑ i ∈ Finset.range n,
        (((n + 1).choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
      = (∑ i ∈ Finset.range n, ((n.choose i : ℕ) : S) * (u (i + 1) * v (n - i)))
        + (∑ i ∈ Finset.range n, ((n.choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hc : ((n + 1).choose (i + 1) : ℕ) = n.choose i + n.choose (i + 1) :=
      Nat.choose_succ_succ n i
    rw [hc]
    push_cast
    ring
  rw [e1, e2, e3, e4, e5]
  ring

private theorem iterate_derivation_mul {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    (D : Derivation B S S) (n : ℕ) (x y : S) :
    (⇑D)^[n] (x * y)
      = ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : S) * ((⇑D)^[i] x * (⇑D)^[n - i] y) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : ∀ i ∈ Finset.range (n + 1),
          D (((n.choose i : ℕ) : S) * ((⇑D)^[i] x * (⇑D)^[n - i] y))
            = ((n.choose i : ℕ) : S) * ((⇑D)^[i + 1] x * (⇑D)^[n - i] y)
              + ((n.choose i : ℕ) : S) * ((⇑D)^[i] x * (⇑D)^[n + 1 - i] y) := by
        intro i hi
        rw [Finset.mem_range] at hi
        have e1 : D ((⇑D)^[i] x) = (⇑D)^[i + 1] x := (Function.iterate_succ_apply' (⇑D) i x).symm
        have e2 : D ((⇑D)^[n - i] y) = (⇑D)^[n + 1 - i] y := by
          have hni : n + 1 - i = n - i + 1 := by omega
          rw [hni]
          exact (Function.iterate_succ_apply' (⇑D) (n - i) y).symm
        rw [derivation_natCast_mul, D.leibniz, e1, e2]
        simp only [smul_eq_mul]
        ring
      rw [Function.iterate_succ_apply', ih, map_sum]
      refine Eq.trans (Finset.sum_congr rfl hstep) ?_
      rw [Finset.sum_add_distrib]
      exact sum_choose_succ_mul_eq (fun i => (⇑D)^[i] x) (fun i => (⇑D)^[i] y) n

private theorem multiIndexDeriv_succ {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    {m : ℕ} (D : Fin (m + 1) → Derivation B S S) (α : Fin (m + 1) → ℕ) (x : S) :
    multiIndexDeriv D α x
      = (⇑(D 0))^[α 0] (multiIndexDeriv (fun i => D i.succ) (fun i => α i.succ) x) := by
  simp only [multiIndexDeriv, Fin.foldr_succ]

private theorem fin_cons_self_tail {m : ℕ} (β : Fin (m + 1) → ℕ) :
    Fin.cons (β 0) (fun i => β i.succ) = β := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j
    simp

private def finSuccFunEquivProd (m : ℕ) : (Fin (m + 1) → ℕ) ≃ ℕ × (Fin m → ℕ) where
  toFun β := (β 0, fun i => β i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv β := fin_cons_self_tail β
  right_inv p := by
    rcases p with ⟨a, b⟩
    simp

private theorem sum_piFinset_succ {M : Type*} [AddCommMonoid M] {m : ℕ}
    (s : Fin (m + 1) → Finset ℕ) (F : (Fin (m + 1) → ℕ) → M) :
    ∑ β ∈ Fintype.piFinset s, F β
      = ∑ j ∈ s 0, ∑ γ ∈ Fintype.piFinset (fun i => s i.succ), F (Fin.cons j γ) := by
  rw [← Finset.sum_product']
  refine Finset.sum_equiv (finSuccFunEquivProd m) ?_ ?_
  · intro β
    constructor
    · intro hβ
      have hβ' := Fintype.mem_piFinset.1 hβ
      exact Finset.mem_product.2 ⟨hβ' 0, Fintype.mem_piFinset.2 (fun i => hβ' i.succ)⟩
    · intro hβ
      have h1 := Finset.mem_product.1 hβ
      refine Fintype.mem_piFinset.2 (fun i => ?_)
      refine Fin.cases ?_ ?_ i
      · exact h1.1
      · intro j
        exact Fintype.mem_piFinset.1 h1.2 j
  · intro β _
    exact congrArg F (fin_cons_self_tail β).symm

theorem multiIndexDeriv_mul {h : ℕ} (D : Fin h → Derivation k R R) (α : Fin h → ℕ) (f g : R) :
    multiIndexDeriv D α (f * g) =
      ∑ β ∈ Fintype.piFinset fun i => Finset.range (α i + 1),
        ((∏ i, (α i).choose (β i) : ℕ) : R) * multiIndexDeriv D β f *
          multiIndexDeriv D (fun i => α i - β i) g := by
  induction h with
  | zero =>
      have hset : (Fintype.piFinset fun i : Fin 0 => Finset.range (α i + 1))
          = {fun _ => 0} := by
        refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
        · exact Fintype.mem_piFinset.2 (fun i => i.elim0)
        · intro x _
          funext i
          exact i.elim0
      rw [hset, Finset.sum_singleton]
      simp
  | succ h ih =>
      have hcons : ∀ (j : ℕ) (γ : Fin h → ℕ) (x : R),
          multiIndexDeriv D (Fin.cons j γ) x
            = (⇑(D 0))^[j] (multiIndexDeriv (fun i => D i.succ) γ x) := by
        intro j γ x
        rw [multiIndexDeriv_succ D (Fin.cons j γ) x]
        simp
      have hcons2 : ∀ (j : ℕ) (γ : Fin h → ℕ) (x : R),
          multiIndexDeriv D (fun i => α i - (Fin.cons j γ : Fin (h + 1) → ℕ) i) x
            = (⇑(D 0))^[α 0 - j]
                (multiIndexDeriv (fun i => D i.succ) (fun i => α i.succ - γ i) x) := by
        intro j γ x
        rw [multiIndexDeriv_succ D (fun i => α i - (Fin.cons j γ : Fin (h + 1) → ℕ) i) x]
        simp
      have key : ∀ γ : Fin h → ℕ,
          (⇑(D 0))^[α 0] (((∏ i, (α i.succ).choose (γ i) : ℕ) : R)
              * multiIndexDeriv (fun i => D i.succ) γ f
              * multiIndexDeriv (fun i => D i.succ) (fun i => α i.succ - γ i) g)
            = ∑ j ∈ Finset.range (α 0 + 1),
                ((∏ i, (α i).choose ((Fin.cons j γ : Fin (h + 1) → ℕ) i) : ℕ) : R)
                  * multiIndexDeriv D (Fin.cons j γ) f
                  * multiIndexDeriv D (fun i => α i - (Fin.cons j γ : Fin (h + 1) → ℕ) i) g := by
        intro γ
        have hA : ((∏ i, (α i.succ).choose (γ i) : ℕ) : R)
              * multiIndexDeriv (fun i => D i.succ) γ f
              * multiIndexDeriv (fun i => D i.succ) (fun i => α i.succ - γ i) g
            = ((∏ i, (α i.succ).choose (γ i) : ℕ) : R)
              * (multiIndexDeriv (fun i => D i.succ) γ f
                * multiIndexDeriv (fun i => D i.succ) (fun i => α i.succ - γ i) g) :=
          mul_assoc _ _ _
        rw [hA, iterate_derivation_natCast_mul, iterate_derivation_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hcons j γ f, hcons2 j γ g, Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        push_cast
        ring
      rw [multiIndexDeriv_succ D α (f * g), ih (fun i => D i.succ) (fun i => α i.succ),
        iterate_derivation_sum]
      refine Eq.trans (Finset.sum_congr rfl (fun γ _ => key γ)) ?_
      rw [Finset.sum_comm]
      exact (sum_piFinset_succ (fun i : Fin (h + 1) => Finset.range (α i + 1))
        (fun β => ((∏ i, (α i).choose (β i) : ℕ) : R) * multiIndexDeriv D β f *
          multiIndexDeriv D (fun i => α i - β i) g)).symm

theorem multiIndexDeriv_mul_sub_sum_mem {h : ℕ} (D : Fin h → Derivation k R R) (J : Ideal R)
    (r s : ℕ) (α : Fin h → ℕ) (hα : ∑ i, α i = r + s) {f g : R}
    (hf : f ∈ J ^ r) (hg : g ∈ J ^ s) :
    multiIndexDeriv D α (f * g) -
        ∑ β ∈ (Fintype.piFinset fun i => Finset.range (α i + 1)).filter
            (fun β => ∑ i, β i = r),
          ((∏ i, (α i).choose (β i) : ℕ) : R) * multiIndexDeriv D β f *
            multiIndexDeriv D (fun i => α i - β i) g ∈ J := by
  rw [multiIndexDeriv_mul D α f g,
    ← Finset.sum_filter_add_sum_filter_not
      (Fintype.piFinset fun i => Finset.range (α i + 1)) (fun β => ∑ i, β i = r),
    add_sub_cancel_left]
  refine Ideal.sum_mem _ ?_
  intro β hβ
  rw [Finset.mem_filter] at hβ
  obtain ⟨hβmem, hβne⟩ := hβ
  have hβi : ∀ i, β i ≤ α i := fun i =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Fintype.mem_piFinset.mp hβmem i))
  have h1 : (∑ i, (α i - β i)) + ∑ i, β i = r + s := by
    rw [← hα, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hβi i)
  by_cases hlt : ∑ i, β i < r
  · have hmem : multiIndexDeriv D β f ∈ J ^ (r - ∑ i, β i) :=
      multiIndexDeriv_mem_pow_sub D J r hf β
    have hx : multiIndexDeriv D β f ∈ J := by
      have hpos : 0 < r - ∑ i, β i := by omega
      exact Ideal.pow_le_self hpos.ne' hmem
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hx)
  · have hmem : multiIndexDeriv D (fun i => α i - β i) g ∈ J ^ (s - ∑ i, (α i - β i)) :=
      multiIndexDeriv_mem_pow_sub D J s hg (fun i => α i - β i)
    have hy : multiIndexDeriv D (fun i => α i - β i) g ∈ J := by
      have hpos : 0 < s - ∑ i, (α i - β i) := by omega
      exact Ideal.pow_le_self hpos.ne' hmem
    exact Ideal.mul_mem_left _ _ hy

private theorem foldr_comm_of_comm {A : Type*} (E : A → A) :
    ∀ (n : ℕ) (F : Fin n → A → A), (∀ (i : Fin n) (y : A), E (F i y) = F i (E y)) →
      ∀ x : A, E (Fin.foldr n F x) = Fin.foldr n F (E x) := by
  intro n
  induction n with
  | zero =>
      intro F _ x
      simp
  | succ n ih =>
      intro F hF x
      rw [Fin.foldr_succ, Fin.foldr_succ, hF 0,
        ih (fun i => F i.succ) (fun i y => hF i.succ y) x]

private theorem multiIndexDeriv_add_of_comm_forall :
    ∀ (n : ℕ) (D : Fin n → Derivation k R R),
      (∀ i j : Fin n, ∀ x : R, D i (D j x) = D j (D i x)) →
      ∀ (α β : Fin n → ℕ) (x : R),
        multiIndexDeriv D (α + β) x = multiIndexDeriv D α (multiIndexDeriv D β x) := by
  intro n
  induction n with
  | zero =>
      intro D _ α β x
      simp
  | succ n ih =>
      intro D hD α β x
      have key : ∀ (γ : Fin (n + 1) → ℕ) (y : R),
          multiIndexDeriv D γ y =
            (⇑(D 0))^[γ 0]
              (multiIndexDeriv (fun i : Fin n => D i.succ) (fun i : Fin n => γ i.succ) y) := by
        intro γ y
        exact Fin.foldr_succ (fun (i : Fin (n + 1)) (z : R) => (⇑(D i))^[γ i] z) y
      have hcomm0 : ∀ (γ : Fin n → ℕ) (y : R),
          (⇑(D 0)) (multiIndexDeriv (fun i : Fin n => D i.succ) γ y) =
            multiIndexDeriv (fun i : Fin n => D i.succ) γ ((⇑(D 0)) y) := by
        intro γ y
        have hc : ∀ (i : Fin n) (z : R),
            (⇑(D 0)) ((⇑(D i.succ))^[γ i] z) = (⇑(D i.succ))^[γ i] ((⇑(D 0)) z) := by
          intro i z
          have hcomm : Function.Commute (⇑(D 0) : R → R) (⇑(D i.succ) : R → R) :=
            fun w => hD 0 i.succ w
          exact hcomm.iterate_right (γ i) z
        exact foldr_comm_of_comm (⇑(D 0)) n (fun i z => (⇑(D i.succ))^[γ i] z) hc y
      have hcomm : ∀ (m : ℕ) (γ : Fin n → ℕ) (y : R),
          (⇑(D 0))^[m] (multiIndexDeriv (fun i : Fin n => D i.succ) γ y) =
            multiIndexDeriv (fun i : Fin n => D i.succ) γ ((⇑(D 0))^[m] y) := by
        intro m γ y
        have hc : Function.Commute (multiIndexDeriv (fun i : Fin n => D i.succ) γ)
            (⇑(D 0) : R → R) := fun w => (hcomm0 γ w).symm
        exact (hc.iterate_right m y).symm
      have hidx : (fun i : Fin n => (α + β) i.succ)
          = (fun i : Fin n => α i.succ) + (fun i : Fin n => β i.succ) := by
        funext i
        simp
      rw [key (α + β) x, hidx,
        ih (fun i : Fin n => D i.succ) (fun i j w => hD i.succ j.succ w)
          (fun i : Fin n => α i.succ) (fun i : Fin n => β i.succ) x,
        key β x, key α, Pi.add_apply, Function.iterate_add_apply,
        hcomm (β 0) (fun i : Fin n => α i.succ)
          (multiIndexDeriv (fun i : Fin n => D i.succ) (fun i : Fin n => β i.succ) x)]

theorem multiIndexDeriv_add {h : ℕ} (D : Fin h → Derivation k R R)
    (hD : ∀ i j : Fin h, ∀ x : R, D i (D j x) = D j (D i x)) (α β : Fin h → ℕ) (x : R) :
    multiIndexDeriv D (α + β) x = multiIndexDeriv D α (multiIndexDeriv D β x) :=
  multiIndexDeriv_add_of_comm_forall h D hD α β x

def unitMultiIndex {h : ℕ} (i : Fin h) : Fin h → ℕ := fun j => if j = i then 1 else 0

@[simp]
theorem unitMultiIndex_apply {h : ℕ} (i j : Fin h) :
    unitMultiIndex i j = if j = i then 1 else 0 := rfl

theorem sum_unitMultiIndex {h : ℕ} (i : Fin h) : ∑ j, unitMultiIndex i j = 1 := by
  simp [unitMultiIndex]

private theorem foldr_eq_of_eq_id_of_ne {A : Type*} :
    ∀ (n : ℕ) (F : Fin n → A → A) (i : Fin n) (f : A → A),
      (∀ j : Fin n, j ≠ i → ∀ y : A, F j y = y) → (∀ y : A, F i y = f y) →
      ∀ x : A, Fin.foldr n F x = f x := by
  intro n
  induction n with
  | zero =>
      intro F i
      exact i.elim0
  | succ m ih =>
      intro F i
      induction i using Fin.cases with
      | zero =>
          intro f hne heq x
          have hinner : Fin.foldr m (fun j : Fin m => F j.succ) x = x :=
            foldr_eq_self_of_forall_eq_self m (fun j : Fin m => F j.succ)
              (fun j y => hne j.succ (Fin.succ_ne_zero j) y) x
          rw [Fin.foldr_succ]
          show F 0 (Fin.foldr m (fun j : Fin m => F j.succ) x) = f x
          rw [hinner]
          exact heq x
      | succ j =>
          intro f hne heq x
          have hinner : Fin.foldr m (fun j' : Fin m => F j'.succ) x = f x :=
            ih (fun j' : Fin m => F j'.succ) j f
              (fun j' hj' y => hne j'.succ (fun hc => hj' (Fin.succ_injective m hc)) y)
              (fun y => heq y) x
          rw [Fin.foldr_succ]
          show F 0 (Fin.foldr m (fun j' : Fin m => F j'.succ) x) = f x
          rw [hinner]
          exact hne 0 (Ne.symm (Fin.succ_ne_zero j)) (f x)

theorem multiIndexDeriv_unitMultiIndex {h : ℕ} (D : Fin h → Derivation k R R) (i : Fin h) (x : R) :
    multiIndexDeriv D (unitMultiIndex i) x = D i x := by
  show Fin.foldr h (fun j y => (⇑(D j))^[unitMultiIndex i j] y) x = D i x
  refine foldr_eq_of_eq_id_of_ne h (fun j y => (⇑(D j))^[unitMultiIndex i j] y) i
    (⇑(D i)) ?_ ?_ x
  · intro j hj y
    simp [unitMultiIndex, hj]
  · intro y
    simp [unitMultiIndex]

theorem multiIndexDeriv_add_unitMultiIndex_apply_first {h : ℕ} (D : Fin h → Derivation k R R)
    (hD : ∀ i j : Fin h, ∀ x : R, D i (D j x) = D j (D i x)) (α : Fin h → ℕ) (i : Fin h) (x : R) :
    multiIndexDeriv D (α + unitMultiIndex i) x = multiIndexDeriv D α (D i x) := by
  rw [multiIndexDeriv_add D hD α (unitMultiIndex i) x, multiIndexDeriv_unitMultiIndex D i x]

end

end FunctorialResolution.EmbeddedResolution
