import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.LevelBasis

variable {A L Q : Type} [CommRing A] [CommRing L] [CommRing Q] (s : A →+* L) (i : L →+* Q) (J : Ideal A)
  {ι : Type} (m : ι → L)

def lsum (c : ι →₀ A) : L := c.sum fun k a => s a * m k

theorem lsum_add (c c' : ι →₀ A) : lsum s m (c + c') = lsum s m c + lsum s m c' :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])

theorem lsum_sub (c c' : ι →₀ A) : lsum s m (c - c') = lsum s m c - lsum s m c' :=
  Finsupp.sum_sub_index (fun _ _ _ => by rw [map_sub, sub_mul])

theorem lsum_smul (a : A) (c : ι →₀ A) : lsum s m (a • c) = s a * lsum s m c := by
  unfold lsum
  rw [Finsupp.sum_smul_index (fun _ => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [map_mul, mul_assoc]

theorem lsum_single (k : ι) : lsum s m (Finsupp.single k 1) = m k := by
  unfold lsum; rw [Finsupp.sum_single_index (by simp), map_one, one_mul]

def IsApprox (n : ℕ) (x : Q) (c : ι →₀ A) : Prop := x - i (lsum s m c) ∈ (J ^ n).map (i.comp s)

theorem map_pow_eq (n : ℕ) : (J ^ n).map (i.comp s) = ((J.map s) ^ n).map i := by
  rw [← Ideal.map_map, Ideal.map_pow]

variable {s i J m}

theorem IsApprox.mono {n n' : ℕ} {x : Q} {c : ι →₀ A} (h : n' ≤ n) (hc : IsApprox s i J m n x c) :
    IsApprox s i J m n' x c :=
  Ideal.map_mono (Ideal.pow_le_pow_right h) hc

theorem exists_approx (hc : IsCompl i (J.map s))
    (H1 : ∀ (n : ℕ) (x : L), ∃ c : ι →₀ A, x - c.sum (fun k a => s a * m k) ∈ (J ^ n).map s)
    (n : ℕ) (x : Q) : ∃ c, IsApprox s i J m n x c := by
  obtain ⟨a, ha⟩ := hc.surj x n
  obtain ⟨c, hc'⟩ := H1 n a
  refine ⟨c, ?_⟩
  unfold IsApprox
  have e : x - i (lsum s m c) = (x - i a) + i (a - lsum s m c) := by rw [map_sub]; ring
  rw [e, map_pow_eq]
  refine add_mem ha (Ideal.mem_map_of_mem i ?_)
  rw [← Ideal.map_pow]; exact hc'

theorem approx_unique (hc : IsCompl i (J.map s))
    (H2 : ∀ (n : ℕ) (c : ι →₀ A), c.sum (fun k a => s a * m k) ∈ (J ^ n).map s → ∀ k, c k ∈ J ^ n)
    {n : ℕ} {x : Q} {c c' : ι →₀ A} (h : IsApprox s i J m n x c) (h' : IsApprox s i J m n x c') (k : ι) :
    c k - c' k ∈ J ^ n := by
  have h3 := sub_mem h' h
  have e : x - i (lsum s m c') - (x - i (lsum s m c)) = i (lsum s m (c - c')) := by
    rw [lsum_sub, map_sub]; ring
  rw [e, map_pow_eq] at h3
  have h4 := hc.ker _ n h3
  rw [← Ideal.map_pow] at h4
  simpa using H2 n (c - c') h4 k

end GlobalTheory.BSP.LevelBasis

open GlobalTheory.BSP.LevelBasis in

theorem GlobalTheory.BSP.exists_topBasis_of_levels (A : Type) [CommRing A] (L : Type) [CommRing L] (Q : Type) [CommRing Q]
    (s : A →+* L) (i : L →+* Q) (J : Ideal A) (ι : Type) (m : ι → L) (k₀ : ι) (h1 : m k₀ = 1)
    (hA : IsAdicComplete J A) (hc : IsCompl i (J.map s))
    (H1 : ∀ (n : ℕ) (x : L), ∃ c : ι →₀ A, x - c.sum (fun k a => s a * m k) ∈ (J ^ n).map s)
    (H2 : ∀ (n : ℕ) (c : ι →₀ A), c.sum (fun k a => s a * m k) ∈ (J ^ n).map s → ∀ k, c k ∈ J ^ n) :
    ∃ tb : TopBasis (i.comp s) J ι, ∀ k, tb.b k = i (m k) := by
  have mt : ∀ n : ℕ, (J ^ n • ⊤ : Submodule A A) = J ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  have exA := exists_approx (m := m) hc H1
  have lim : ∀ (x : Q) (k : ι), ∃ a : A, ∀ n c, IsApprox s i J m n x c → c k - a ∈ J ^ n := by
    intro x k
    choose f hf using exA
    obtain ⟨a, ha⟩ := hA.toIsPrecomplete.prec (f := fun n => f n x k) (fun {p q} hpq => by
      rw [SModEq.sub_mem, mt]
      exact approx_unique hc H2 (hf p x) ((hf q x).mono hpq) k)
    refine ⟨a, fun n c hcn => ?_⟩
    have h2 := ha n
    rw [SModEq.sub_mem, mt] at h2
    have := add_mem (approx_unique hc H2 hcn (hf n x) k) h2
    simpa using this
  choose C hC using lim
  have uniq : ∀ x k a, (∀ n, ∃ c, IsApprox s i J m n x c ∧ c k - a ∈ J ^ n) → C x k = a := by
    intro x k a h
    refine sub_eq_zero.1 (hA.toIsHausdorff.haus _ fun n => ?_)
    rw [SModEq.sub_mem, mt, sub_zero]
    obtain ⟨c, hc1, hc2⟩ := h n
    have := sub_mem hc2 (hC x k n c hc1)
    convert this using 1; ring
  have single_approx : ∀ n k, IsApprox s i J m n (i (m k)) (Finsupp.single k 1) := by
    intro n k; unfold IsApprox; rw [lsum_single, sub_self]; exact zero_mem _
  refine ⟨{
    b := fun k => i (m k)
    c := fun k => AddMonoidHom.mk' (fun x => C x k) (fun x y => uniq (x + y) k _ fun n => by
      obtain ⟨c, hc⟩ := exA n x
      obtain ⟨c', hc'⟩ := exA n y
      refine ⟨c + c', ?_, ?_⟩
      · unfold IsApprox at hc hc' ⊢
        have e : x + y - i (lsum s m (c + c')) = (x - i (lsum s m c)) + (y - i (lsum s m c')) := by
          rw [lsum_add, map_add]; ring
        rw [e]; exact add_mem hc hc'
      · have := add_mem (hC x k n c hc) (hC y k n c' hc')
        convert this using 1; simp only [Finsupp.add_apply]; ring)
    c_mul := fun k a x => by
      simp only [AddMonoidHom.mk'_apply]
      refine uniq _ k _ fun n => ?_
      obtain ⟨c, hc⟩ := exA n x
      refine ⟨a • c, ?_, ?_⟩
      · unfold IsApprox at hc ⊢
        have e : (i.comp s) a * x - i (lsum s m (a • c)) = (i.comp s) a * (x - i (lsum s m c)) := by
          rw [lsum_smul, map_mul, RingHom.comp_apply]; ring
        rw [e]; exact Ideal.mul_mem_left _ _ hc
      · have e : (a • c) k - a * C x k = a * (c k - C x k) := by
          rw [Finsupp.smul_apply, smul_eq_mul]; ring
        rw [e]; exact Ideal.mul_mem_left _ _ (hC x k n c hc)
    c_self := fun k => by
      simp only [AddMonoidHom.mk'_apply]
      exact uniq _ k _ fun n => ⟨_, single_approx n k, by simp⟩
    c_ne := fun j k hjk => by
      simp only [AddMonoidHom.mk'_apply]
      exact uniq _ j _ fun n => ⟨_, single_approx n k, by simp [Finsupp.single_apply, Ne.symm hjk]⟩
    fin := fun x n => by
      obtain ⟨c, hc⟩ := exA n x
      refine c.support.finite_toSet.subset fun k hk => ?_
      simp only [Set.mem_setOf_eq, AddMonoidHom.mk'_apply] at hk
      by_contra h
      simp only [Finset.mem_coe, Finsupp.mem_support_iff, not_not] at h
      have := hC x k n c hc
      rw [h, zero_sub, neg_mem_iff] at this
      exact hk this
    approx := fun x n F hF => by
      classical
      simp only [AddMonoidHom.mk'_apply] at hF ⊢
      obtain ⟨c, hc⟩ := exA n x
      have e1 : i (lsum s m c) = ∑ k ∈ F ∪ c.support, (i.comp s) (c k) * i (m k) := by
        unfold lsum
        rw [Finsupp.sum_of_support_subset c (Finset.subset_union_right (s₁ := F)) _ (fun _ _ => by simp), map_sum]
        simp [RingHom.comp_apply, map_mul]
      have e2 : ∑ k ∈ F, (i.comp s) (C x k) * i (m k) =
          ∑ k ∈ F ∪ c.support, (i.comp s) (if k ∈ F then C x k else 0) * i (m k) := by
        rw [← Finset.sum_subset Finset.subset_union_left (fun k _ hk => by rw [if_neg hk, map_zero, zero_mul])]
        exact Finset.sum_congr rfl fun k hk => by rw [if_pos hk]
      have e3 : x - ∑ k ∈ F, (i.comp s) (C x k) * i (m k) = (x - i (lsum s m c)) +
          ∑ k ∈ F ∪ c.support, (i.comp s) (c k - if k ∈ F then C x k else 0) * i (m k) := by
        rw [e2, e1]; simp only [map_sub, sub_mul, Finset.sum_sub_distrib]; ring
      rw [e3]
      refine add_mem hc (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_))
      by_cases hk : k ∈ F
      · rw [if_pos hk]; exact hC x k n c hc
      · rw [if_neg hk, sub_zero]
        have := add_mem (hC x k n c hc) (hF k hk)
        simpa using this
    complete := by rw [← Ideal.map_map]; exact hc.complete
    i₀ := k₀
    b_i₀ := by simp only [h1, map_one] }, fun k => rfl⟩
