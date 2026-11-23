import Formalism.ThetaLogCoordinates.SandwichModelDomains.SpreadSquare
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDbasisLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDrowLemmas

open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.INST

open Formalism.GradedWeylDivisibility

lemma spr_rowDeg_bidet (R : Type*) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) (m : Fin r × Fin n →₀ ℕ) (hm : m ∈ (bideterminant R sz hsz I).support) (a : Fin r) :
    rowDeg m a = ∑ k : Fin K, ∑ q : Fin (sz k), (Pi.single (I k q) 1 : Fin r → ℕ) a := by
  have h := ldbasis_bidet_rowHom R sz hsz I (mem_support_iff.mp hm)
  rw [← ldrow_weight_rowW, h]
  simp only [Finset.sum_apply]

lemma spr_count_le {r s : ℕ} (I : Fin s → Fin r) (hI : Function.Injective I) (a : Fin r) :
    ∑ q : Fin s, (Pi.single (I q) 1 : Fin r → ℕ) a ≤ if 0 < s then 1 else 0 := by
  classical
  have h1 : ∑ q : Fin s, (Pi.single (I q) 1 : Fin r → ℕ) a
      = (Finset.univ.filter fun q : Fin s => I q = a).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h : I q = a
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [h1]
  by_cases hs : 0 < s
  · rw [if_pos hs, Finset.card_le_one]
    intro x hx y hy
    exact hI ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  · have hs0 : s = 0 := by omega
    subst hs0
    simp

lemma spr_one_le_count {n s : ℕ} (I : Fin s → Fin n) (hI : Function.Injective I) (hs : s = n) (a : Fin n) :
    1 ≤ ∑ q : Fin s, (Pi.single (I q) 1 : Fin n → ℕ) a := by
  classical
  subst hs
  obtain ⟨q, rfl⟩ := (Finite.injective_iff_surjective.mp hI) a
  calc 1 = (Pi.single (I q) 1 : Fin s → ℕ) (I q) := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun q' : Fin s => (Pi.single (I q') 1 : Fin s → ℕ) (I q))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)

lemma spr_bidet_le (R : Type*) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) (hI : ∀ k, Function.Injective (I k)) (l : ℕ)
    (hl : ∀ t : Fin n, shapeDeg sz t ≤ l)
    (m : Fin r × Fin n →₀ ℕ) (hm : m ∈ (bideterminant R sz hsz I).support) (a : Fin r) : rowDeg m a ≤ l := by
  classical
  rw [spr_rowDeg_bidet R sz hsz I m hm a]
  refine (Finset.sum_le_sum fun k _ => spr_count_le (I k) (hI k) a).trans ?_
  rw [← Finset.card_filter]
  by_cases hn : 0 < n
  · exact hl ⟨0, hn⟩
  · have : (Finset.univ.filter fun k : Fin K => 0 < sz k) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun k _ => ?_
      have := hsz k
      omega
    rw [this]
    simp

lemma spr_le_bidet (R : Type*) [CommRing R] {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin n) (hI : ∀ k, Function.Injective (I k)) (lo : ℕ)
    (hlo : ∀ t : Fin n, lo ≤ shapeDeg sz t)
    (m : Fin n × Fin n →₀ ℕ) (hm : m ∈ (bideterminant R sz hsz I).support) (a : Fin n) : lo ≤ rowDeg m a := by
  classical
  rw [spr_rowDeg_bidet R sz hsz I m hm a]
  have hn : n - 1 < n := by have := a.isLt; omega
  refine (hlo ⟨n - 1, hn⟩).trans ?_
  unfold shapeDeg
  rw [Finset.card_filter]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : n - 1 < sz k
  · rw [if_pos hk]
    exact spr_one_le_count (I k) (hI k) (by have := hsz k; omega) a
  · rw [if_neg hk]
    exact Nat.zero_le _

lemma spr_support_induction (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (ν : Fin n → ℕ)
    (P : (Fin r × Fin n →₀ ℕ) → Prop)
    (hP : ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ i, sz i ≤ n) (I : ∀ i, Fin (sz i) → Fin r),
      shapeDeg sz = ν → (∀ i, StrictMono (I i)) → ∀ m ∈ (bideterminant R sz hsz I).support, P m)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) : ∀ m ∈ f.support, P m := by
  classical
  obtain ⟨b, ⟨_, hspan, _⟩, hb⟩ := sSBasis R r n ν
  rw [← hspan] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨_, _, K, sz, hsz, I, hsh, hmono, hbi⟩ := hb i
    rw [hbi]
    exact hP K sz hsz I hsh hmono
  | zero => intro m hm; simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

lemma spr_upper (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (ν : Fin n → ℕ) (l : ℕ) (hl : ∀ t, ν t ≤ l)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) (m : Fin r × Fin n →₀ ℕ)
    (hm : m ∈ f.support) (a : Fin r) : rowDeg m a ≤ l := by
  refine spr_support_induction R r n ν (fun m => rowDeg m a ≤ l) ?_ f hf m hm
  intro K sz hsz I hsh hmono m hm
  exact spr_bidet_le R sz hsz I (fun k => (hmono k).injective) l (by rw [hsh]; exact hl) m hm a

lemma spr_lower (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (ν : Fin n → ℕ) (lo : ℕ) (hlo : ∀ t, lo ≤ ν t)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : f ∈ dualWeyl R n n ν) (m : Fin n × Fin n →₀ ℕ)
    (hm : m ∈ f.support) (a : Fin n) : lo ≤ rowDeg m a := by
  refine spr_support_induction R n n ν (fun m => lo ≤ rowDeg m a) ?_ f hf m hm
  intro K sz hsz I hsh hmono m hm
  exact spr_le_bidet R sz hsz I (fun k => (hmono k).injective) lo (by rw [hsh]; exact hlo) m hm a

theorem spread_top_holds : SpreadTop := by
  intro R _ _ r n ν l hl f hf g _ m hm m' _ a
  exact (spr_upper R r n ν l hl f hf m hm a).trans (Nat.le_add_left _ _)

theorem spread_square_holds : SpreadSquare := by
  intro R _ _ n ν l hl f hf g hg m hm m' hm' a
  have : Nonempty (Fin n) := ⟨a⟩
  obtain ⟨s, hs⟩ := Finite.exists_max ν
  obtain ⟨t, ht⟩ := Finite.exists_min ν
  have h1 := spr_upper R n n ν (ν s) hs f hf m hm a
  have h2 := spr_lower R n ν (ν t) ht g hg m' hm' a
  have h3 := hl s t
  omega

end Formalism.InvariantFactorPaths.INST
