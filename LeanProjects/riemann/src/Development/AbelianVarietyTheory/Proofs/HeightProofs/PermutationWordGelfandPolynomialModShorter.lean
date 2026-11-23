import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SmoothForms.PermWord

section Comm

variable {S : Type} [CommRing S] {n : ℕ}

theorem sum_cons_split {d : ℕ} (f : (Fin (d + 1) → Fin n) → S) :
    ∑ K, f K = ∑ K : Fin d → Fin n, ∑ j : Fin n, f (Fin.cons j K) := by
  rw [Finset.sum_comm, ← (Fin.consEquiv fun _ : Fin (d + 1) => Fin n).sum_comp, Fintype.sum_prod_type]
  rfl

theorem trace_path (X : Matrix (Fin n) (Fin n) S) (k : ℕ) : ∀ Y : Matrix (Fin n) (Fin n) S,
    (Y * X ^ k).trace = ∑ idx : Fin (k + 1) → Fin n,
      Y (idx (Fin.last k)) (idx 0) * ∏ a : Fin k, X (idx a.castSucc) (idx a.succ) := by
  induction k with
  | zero =>
    intro Y
    rw [sum_cons_split]
    simp [Matrix.trace]
  | succ k ih =>
    intro Y
    rw [pow_succ', ← mul_assoc, ih, sum_cons_split (d := k + 1)]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.prod_univ_succ, ← Fin.succ_last]
    simp only [Fin.cons_succ, Fin.cons_zero, Fin.castSucc_zero, ← Fin.succ_castSucc, mul_assoc]

theorem trace_pow_eq [Algebra ℂ S] (X : Fin n → Fin n → S) (k : ℕ) :
    ((Matrix.of X) ^ (k + 1)).trace = gelfA X k := by
  rw [pow_succ', trace_path, gelfA]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [List.prod_ofFn, Fin.prod_univ_castSucc, mul_comm]
  simp [Fin.coeSucc_eq_succ]

theorem perm_sum_mem (X : Matrix (Fin n) (Fin n) S) (T : ℕ → S → Prop) (h0 : T 0 1)
    (hs : ∀ k j p, T j p → T (k + 1 + j) ((X ^ (k + 1)).trace * p)) (d : ℕ) :
    ∀ (π : Equiv.Perm (Fin d)) (m : Fin d → ℕ),
      T (∑ a, (m a + 1)) (∑ K : Fin d → Fin n, ∏ a, (X ^ (m a + 1)) (K (π a)) (K a)) := by
  induction d with
  | zero => intro π m; simpa using h0
  | succ d ih =>
    intro π m
    obtain ⟨⟨p, e⟩, rfl⟩ := Equiv.Perm.decomposeFin.symm.surjective π
    rw [sum_cons_split, Fin.sum_univ_succ]
    simp only [Fin.prod_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
      Equiv.Perm.decomposeFin_symm_apply_succ, Fin.cons_succ, Fin.cons_zero]
    refine Fin.cases ?_ (fun q => ?_) p
    · have := hs (m 0) _ _ (ih e fun a => m a.succ)
      convert this using 1
      simp only [Equiv.swap_self, Equiv.refl_apply, Fin.cons_succ, Fin.cons_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl fun K _ => ?_
      rw [← Finset.sum_mul]; rfl
    · obtain ⟨x, rfl⟩ := e.surjective q
      have := ih e (Function.update (fun a => m a.succ) x (m 0 + 1 + m x.succ))
      convert this using 1
      · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), ← Finset.add_sum_erase _ _ (Finset.mem_univ x),
          Function.update_self, ← add_assoc, ← add_assoc]
        congr 1
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]
      · refine Finset.sum_congr rfl fun K _ => ?_
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ x), Function.update_self, add_assoc (m 0 + 1), pow_add X (m 0 + 1),
          Matrix.mul_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ x), Equiv.swap_apply_right, Fin.cons_succ, Fin.cons_zero,
          mul_assoc]
        congr 2
        refine Finset.prod_congr rfl fun a ha => ?_
        have hne := Finset.ne_of_mem_erase ha
        rw [Function.update_of_ne hne, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (by simpa using hne),
          Fin.cons_succ]

end Comm

section NC

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

def wd {B : Type} [Ring B] (E : Fin n → Fin n → B) (l : List (Fin n × Fin n)) : B := (l.map fun z => E z.1 z.2).prod

theorem wd_append {B : Type} [Ring B] (E : Fin n → Fin n → B) (l l' : List (Fin n × Fin n)) :
    wd E (l ++ l') = wd E l * wd E l' := by simp [wd]

theorem wd_cons {B : Type} [Ring B] (E : Fin n → Fin n → B) (z) (l : List (Fin n × Fin n)) :
    wd E (z :: l) = E z.1 z.2 * wd E l := by simp [wd]

theorem wd_ofFn {B : Type} [Ring B] (E : Fin n → Fin n → B) {d : ℕ} (I K : Fin d → Fin n) :
    wd E (List.ofFn fun a => (I a, K a)) = (List.ofFn fun a => E (I a) (K a)).prod := by
  simp [wd, List.map_ofFn, Function.comp_def]

def shorter (E : Fin n → Fin n → A) (d : ℕ) : Submodule ℂ A :=
  Submodule.span ℂ {x | ∃ l : List (Fin n × Fin n), l.length < d ∧ wd E l = x}

theorem wd_mem_shorter (E : Fin n → Fin n → A) {d : ℕ} {l : List (Fin n × Fin n)} (h : l.length < d) :
    wd E l ∈ shorter E d := Submodule.subset_span ⟨l, h, rfl⟩

theorem shorter_le_filt (E : Fin n → Fin n → A) (d : ℕ) : shorter E d ≤ filt E d := by
  rw [shorter, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  refine Submodule.mem_iSup_of_mem l.length (Submodule.mem_iSup_of_mem hl ?_)
  refine ⟨Matrix.single (fun a => (l.get a).1) (fun a => (l.get a).2) 1, ?_⟩
  conv_rhs => rw [← List.ofFn_get l]
  rw [show (List.ofFn l.get) = List.ofFn fun a => ((l.get a).1, (l.get a).2) from rfl, wd_ofFn]
  simp only [wordMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single (fun a => (l.get a).1), Finset.sum_eq_single (fun a => (l.get a).2)]
  · simp
  · intro K _ hK
    rw [Matrix.single_apply_of_col_ne _ _ hK.symm, zero_smul]
  · simp
  · intro I _ hI
    refine Finset.sum_eq_zero fun K _ => ?_
    rw [Matrix.single_apply_of_row_ne hI.symm, zero_smul]
  · simp

theorem mul_mem_shorter (E : Fin n → Fin n → A) {d : ℕ} (z : Fin n × Fin n) {x : A} (hx : x ∈ shorter E d) :
    E z.1 z.2 * x ∈ shorter E (d + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    rw [← wd_cons]
    exact wd_mem_shorter E (by simpa using hl)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem perm_sub_mem {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E) {l l' : List (Fin n × Fin n)} (h : l.Perm l') :
    wd E l - wd E l' ∈ shorter E l.length := by
  induction h with
  | nil => simp
  | cons z _ ih => rw [wd_cons, wd_cons, ← mul_sub]; exact mul_mem_shorter E z ih
  | swap x y l =>
    simp only [wd_cons]
    rw [← mul_assoc, ← mul_assoc, ← sub_mul, hE, sub_mul]
    refine sub_mem ?_ ?_
    · split_ifs
      · exact wd_mem_shorter E (l := (y.1, x.2) :: l) (by simp)
      · simp
    · split_ifs
      · exact wd_mem_shorter E (l := (x.1, y.2) :: l) (by simp)
      · simp
  | trans h1 _ ih1 ih2 =>
    rw [← h1.length_eq] at ih2
    simpa using add_mem ih1 ih2

def gen (n : ℕ) (a b : Fin n) : MvPolynomial (Fin n × Fin n) ℂ := MvPolynomial.X (a, b)

theorem wd_gen (l : List (Fin n × Fin n)) :
    wd (gen n) l = MvPolynomial.monomial (Multiset.toFinsupp (l : Multiset (Fin n × Fin n))) 1 := by
  induction l with
  | nil => simp [wd]
  | cons z l ih =>
    rw [wd_cons, ih, gen, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, ← Multiset.cons_coe,
      ← Multiset.singleton_add, map_add, Multiset.toFinsupp_singleton]

def order (E : Fin n → Fin n → A) : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] A :=
  (MvPolynomial.basisMonomials (Fin n × Fin n) ℂ).constr ℂ fun s => wd E (Finsupp.toMultiset s).toList

theorem order_wd (E : Fin n → Fin n → A) (l : List (Fin n × Fin n)) :
    order E (wd (gen n) l) = wd E (l : Multiset (Fin n × Fin n)).toList := by
  rw [wd_gen, ← congrFun (MvPolynomial.coe_basisMonomials (Fin n × Fin n) ℂ), order, Module.Basis.constr_basis]
  simp

def symb (E : Fin n → Fin n → A) (d : ℕ) : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ × A) :=
  Submodule.span ℂ {x | ∃ l : List (Fin n × Fin n), l.length = d ∧ (wd (gen n) l, wd E l) = x}

theorem symb_mul (E : Fin n → Fin n → A) {a b : ℕ} {x y} (hx : x ∈ symb E a) (hy : y ∈ symb E b) :
    x * y ∈ symb E (a + b) := by
  have := Submodule.mul_mem_mul hx hy
  rw [symb, symb, Submodule.span_mul_span] at this
  refine Submodule.span_mono ?_ this
  rintro _ ⟨_, ⟨l, rfl, rfl⟩, _, ⟨l', rfl, rfl⟩, rfl⟩
  exact ⟨l ++ l', by simp, by simp [wd_append]⟩

theorem symb_sub {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E) {d : ℕ} {x} (hx : x ∈ symb E d) :
    x.2 - order E x.1 ∈ shorter E d := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl, rfl⟩ := hx
    simp only [order_wd]
    exact perm_sub_mem hE (Multiset.coe_eq_coe.1 (Multiset.coe_toList _).symm)
  | zero => simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    simp only [Prod.snd_add, Prod.fst_add, map_add]; abel
  | smul c x _ hx =>
    convert Submodule.smul_mem _ c hx using 1
    simp [smul_sub]

theorem sum_mem_symb (E : Fin n → Fin n → A) {d : ℕ} {ι : Type} [Fintype ι] (I K : ι → Fin d → Fin n) :
    (∑ i, (List.ofFn fun a => gen n (I i a) (K i a)).prod, ∑ i, (List.ofFn fun a => E (I i a) (K i a)).prod) ∈
      symb E d := by
  rw [prod_mk_sum]
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨List.ofFn fun a => (I i a, K i a), by simp, ?_⟩
  rw [wd_ofFn, wd_ofFn]

end NC

theorem wordMap_permMat {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (d : ℕ)
    (π : Equiv.Perm (Fin d)) :
    wordMap E d (permMat n d π) = ∑ K : Fin d → Fin n, (List.ofFn fun a => E (K (π a)) (K a)).prod := by
  simp only [wordMap, permMat, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [Finset.sum_eq_single (K ∘ π)]
  · simp
  · intro I _ hI; rw [if_neg hI, zero_smul]
  · simp

theorem exists_symb {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (d : ℕ)
    (π : Equiv.Perm (Fin d)) : ∃ c ∈ Algebra.adjoin ℂ (Set.range (gelfA E)),
      (∑ K : Fin d → Fin n, (List.ofFn fun a => gen n (K (π a)) (K a)).prod, c) ∈ symb E d := by
  have key := perm_sum_mem (Matrix.of (gen n))
    (fun j p => ∃ c ∈ Algebra.adjoin ℂ (Set.range (gelfA E)), (p, c) ∈ symb E j)
    ⟨1, one_mem _, Submodule.subset_span ⟨[], rfl, by simp [wd]⟩⟩
    (by
      rintro k j p ⟨c, hc, h⟩
      refine ⟨gelfA E k * c, mul_mem (Algebra.subset_adjoin ⟨k, rfl⟩) hc, ?_⟩
      rw [trace_pow_eq, ← Prod.mk_mul_mk]
      refine symb_mul E ?_ h
      unfold gelfA
      exact sum_mem_symb E (fun idx : Fin (k + 1) → Fin n => idx) fun idx a => idx (a + 1))
    d π (fun _ => 0)
  simp only [zero_add, pow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
    Matrix.of_apply] at key
  simp only [List.prod_ofFn]
  exact key

theorem permWord : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → ∀ (d : ℕ) (π : Equiv.Perm (Fin d)), ∃ c ∈ Algebra.adjoin ℂ (Set.range (gelfA E)), wordMap E d (permMat n d π) - c ∈ filt E d := by
  intro A _ _ n E hE d π
  obtain ⟨c, hc, h⟩ := exists_symb E d π
  refine ⟨c, hc, shorter_le_filt E d ?_⟩
  have h2 := symb_sub hE (sum_mem_symb E (fun (K : Fin d → Fin n) a => K (π a)) fun K => K)
  have h1 := symb_sub hE h
  have h3 := sub_mem h2 h1
  rw [sub_sub_sub_cancel_right] at h3
  rw [wordMap_permMat]
  exact h3

end GlobalTheory.SmoothForms.PermWord

end
