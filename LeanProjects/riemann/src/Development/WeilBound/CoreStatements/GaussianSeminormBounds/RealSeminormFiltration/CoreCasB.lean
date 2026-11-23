import Mathlib

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

variable {K I : Type} {M : Type} [AddCommGroup M] [Module ℂ M] {V : Type} [AddCommGroup V] [Module ℂ V]

def wordX (X : I → Module.End ℂ M) (l : List I) : Module.End ℂ M := (l.map X).prod

def filtX (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ (l : List I) (v : V), l.length ≤ n ∧ y = wordX X l (ι v)}

theorem wordX_cons (X : I → Module.End ℂ M) (a : I) (l : List I) (y : M) :
    wordX X (a :: l) y = X a (wordX X l y) := by
  simp [wordX]

theorem filtX_zero (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) : filtX X ι 0 = LinearMap.range ι := by
  apply le_antisymm
  · rw [filtX, Submodule.span_le]
    rintro _ ⟨l, v, hl, rfl⟩
    have : l = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)
    subst this
    exact ⟨v, by simp [wordX]⟩
  · rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨[], v, le_rfl, by simp [wordX]⟩

theorem filtX_mono (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) {m n : ℕ} (h : m ≤ n) :
    filtX X ι m ≤ filtX X ι n := by
  refine Submodule.span_mono ?_
  rintro _ ⟨l, v, hl, rfl⟩
  exact ⟨l, v, hl.trans h, rfl⟩

theorem filtX_X (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) (i : I) :
    ∀ x ∈ filtX X ι n, X i x ∈ filtX X ι (n + 1) := by
  have : filtX X ι n ≤ (filtX X ι (n + 1)).comap (X i) := by
    rw [filtX, Submodule.span_le]
    rintro _ ⟨l, v, hl, rfl⟩
    exact Submodule.subset_span ⟨i :: l, v, by simpa using hl, (wordX_cons X i l _).symm⟩
  exact fun x hx => this hx

theorem filtX_fd [Fintype I] [FiniteDimensional ℂ V] (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) :
    FiniteDimensional ℂ (filtX X ι n) := by
  induction n with
  | zero => rw [filtX_zero]; infer_instance
  | succ n ih =>
    classical
    have hle : filtX X ι (n + 1) ≤ filtX X ι n ⊔ ⨆ i, (filtX X ι n).map (X i) := by
      rw [filtX, Submodule.span_le]
      rintro _ ⟨l, v, hl, rfl⟩
      cases l with
      | nil => exact Submodule.mem_sup_left (Submodule.subset_span ⟨[], v, Nat.zero_le _, rfl⟩)
      | cons a l =>
        refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a ?_)
        exact ⟨wordX X l (ι v), Submodule.subset_span ⟨l, v, by simpa using hl, rfl⟩, (wordX_cons X a l _).symm⟩
    exact Submodule.finiteDimensional_of_le hle

theorem filtX_succ_le (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) :
    filtX X ι (n + 1) ≤ filtX X ι n ⊔
      Submodule.span ℂ {y | ∃ (w : Fin (n + 1) → I) (v : V), y = wordX X (List.ofFn w) (ι v)} := by
  conv_lhs => rw [filtX]
  rw [Submodule.span_le]
  rintro _ ⟨l, v, hl, rfl⟩
  by_cases h : l.length ≤ n
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨l, v, h, rfl⟩)
  · have h' : l.length = n + 1 := by omega
    refine Submodule.mem_sup_right (Submodule.subset_span ⟨fun i => l.get (i.cast h'.symm), v, ?_⟩)
    congr 2
    apply List.ext_getElem
    · simp [h']
    · intro m h1 h2
      rw [List.getElem_ofFn]
      simp

theorem filtX_e [Fintype I] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M) (c : K → Matrix I I ℂ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j) (ρ : K → Module.End ℂ V)
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v)) (n : ℕ) (k : K) :
    ∀ x ∈ filtX X ι n, e k x ∈ filtX X ι n := by
  have key : ∀ (l : List I) (v : V), e k (wordX X l (ι v)) ∈ filtX X ι l.length := by
    intro l v
    induction l with
    | nil =>
      have : e k (wordX X [] (ι v)) = wordX X [] (ι (ρ k v)) := by simp [wordX, hι]
      rw [this]
      exact Submodule.subset_span ⟨[], _, le_rfl, rfl⟩
    | cons a l ih =>
      have h := LinearMap.congr_fun (h1 k a) (wordX X l (ι v))
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] at h
      rw [wordX_cons, sub_eq_iff_eq_add.1 h, List.length_cons]
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
        (filtX_X X ι _ a _ ih)
      exact filtX_X X ι _ j _ (Submodule.subset_span ⟨l, v, le_rfl, rfl⟩)
  have : filtX X ι n ≤ (filtX X ι n).comap (e k) := by
    conv_lhs => rw [filtX]
    rw [Submodule.span_le]
    rintro _ ⟨l, v, hl, rfl⟩
    exact filtX_mono X ι hl (key l v)
  exact fun x hx => this hx

theorem filtX_perm [Fintype I] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M) (c : K → Matrix I I ℂ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j)
    (h2 : ∀ i j, X i * X j - X j * X i ∈ Submodule.span ℂ (Set.range e)) (ρ : K → Module.End ℂ V)
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v)) {l l' : List I} (h : l.Perm l') (n : ℕ)
    (hn : l.length ≤ n + 1) (v : V) : wordX X l (ι v) - wordX X l' (ι v) ∈ filtX X ι n := by
  induction h generalizing n with
  | nil => simp
  | @cons a l l' hp ih =>
    rw [wordX_cons, wordX_cons, ← map_sub]
    cases n with
    | zero =>
      have h0 : l = [] := List.length_eq_zero_iff.1 (by simpa using hn)
      subst h0
      have h0' : l' = [] := hp.nil_eq.symm
      subst h0'
      simp
    | succ n => exact filtX_X X ι n a _ (ih n (by simpa using hn))
  | swap a b l =>
    have hl : l.length ≤ n := by simp only [List.length_cons] at hn; omega
    have hm : wordX X l (ι v) ∈ filtX X ι n := Submodule.subset_span ⟨l, v, hl, rfl⟩
    have hall : ∀ E ∈ Submodule.span ℂ (Set.range e), E (wordX X l (ι v)) ∈ filtX X ι n := by
      intro E hE
      induction hE using Submodule.span_induction with
      | mem E hE =>
        obtain ⟨k, rfl⟩ := hE
        exact filtX_e e X c h1 ρ ι hι n k _ hm
      | zero => simp
      | add E F _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
      | smul a E _ h1 => exact Submodule.smul_mem _ a h1
    simp only [wordX_cons]
    exact hall _ (h2 b a)
  | trans p1 p2 ih1 ih2 =>
    have := Submodule.add_mem _ (ih1 n hn) (ih2 n (p1.length_eq ▸ hn))
    rwa [sub_add_sub_cancel] at this

theorem wordX_comm [Fintype I] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M) (c : K → Matrix I I ℂ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j) (k : K) (n : ℕ) (w : Fin n → I) :
    e k * wordX X (List.ofFn w) = wordX X (List.ofFn w) * e k +
      ∑ i, ∑ j, c k j (w i) • wordX X (List.ofFn (Function.update w i j)) := by
  induction n with
  | zero => simp [wordX]
  | succ n ih =>
    have hc : ∀ (a : I) (l : List I), wordX X (a :: l) = X a * wordX X l := fun a l => by simp [wordX]
    have u0 : ∀ j, List.ofFn (Function.update w 0 j) = j :: List.ofFn (fun i : Fin n => w i.succ) := by
      intro j
      rw [List.ofFn_succ]
      simp [Function.update_of_ne (Fin.succ_ne_zero _)]
    have us : ∀ (i : Fin n) j, List.ofFn (Function.update w i.succ j) =
        w 0 :: List.ofFn (Function.update (fun i : Fin n => w i.succ) i j) := by
      intro i j
      rw [List.ofFn_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm]
      congr 2
      funext m
      by_cases hm : m = i
      · subst hm; simp
      · rw [Function.update_of_ne hm, Function.update_of_ne (fun h => hm (Fin.succ_injective _ h))]
    rw [Fin.sum_univ_succ]
    simp only [u0, us, hc]
    rw [List.ofFn_succ, hc, ← mul_assoc, sub_eq_iff_eq_add.1 (h1 k (w 0)), add_mul, mul_assoc,
      ih (fun i => w i.succ), mul_add, Finset.sum_mul, Finset.mul_sum]
    simp only [Finset.mul_sum, mul_smul_comm, smul_mul_assoc, mul_assoc]
    abel

end PositivityTheory.KReal

end
