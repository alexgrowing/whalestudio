import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl

namespace GlobalTheory.ArtinSpan

section General

open Polynomial

variable {R Q : Type*} [CommRing R] [CommRing Q] [Algebra R Q] {N : ℕ}

def artinSpan (R : Type*) [CommRing R] [Algebra R Q] (x : Fin N → Q) (j : ℕ) : Submodule R Q :=
  Submodule.span R {a | ∃ m : Fin N → ℕ, (∀ i, m i ≤ (i : ℕ)) ∧ (∀ i : Fin N, (i : ℕ) < j → m i = 0) ∧
    a = ∏ i, x i ^ m i}

theorem exists_monic (x : Fin N → Q) (hx : ∏ l, (X - C (x l)) = (X : Q[X]) ^ N) (j : Fin N) :
    ∃ g : (Algebra.adjoin R (x '' {l | (j : ℕ) + 1 ≤ (l : ℕ)}))[X],
      g.Monic ∧ g.natDegree ≤ (j : ℕ) + 1 ∧ aeval (x j) g = 0 := by
  classical
  set A := Algebra.adjoin R (x '' {l | (j : ℕ) + 1 ≤ (l : ℕ)}) with hA
  let y : Fin N → A := fun l => if h : (j : ℕ) + 1 ≤ (l : ℕ) then
    ⟨x l, Algebra.subset_adjoin ⟨l, h, rfl⟩⟩ else 0
  let q : A[X] := ∏ l ∈ Finset.Ioi j, (X - C (y l))
  have hq : q.Monic := monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _
  have hqm : q.map (algebraMap A Q) = ∏ l ∈ Finset.Ioi j, (X - C (x l)) := by
    simp only [q, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun l hl => ?_
    have h : (j : ℕ) + 1 ≤ (l : ℕ) := Finset.mem_Ioi.1 hl
    have h' : j < l := Finset.mem_Ioi.1 hl
    simp [y, h']
  have hsplit : (∏ l ∈ Finset.Ioi j, (X - C (x l))) * ∏ l ∈ Finset.Iic j, (X - C (x l))
      = (X : Q[X]) ^ N := by
    rw [← hx, ← Finset.prod_union]
    · congr 1
      ext l
      simp [lt_or_ge]
    · rw [Finset.disjoint_left]
      intro l h1 h2
      exact absurd (Finset.mem_Iic.1 h2) (not_le.2 (Finset.mem_Ioi.1 h1))
  have hg : (X ^ N /ₘ q).map (algebraMap A Q) = ∏ l ∈ Finset.Iic j, (X - C (x l)) := by
    rw [map_divByMonic _ hq, Polynomial.map_pow, map_X, ← hsplit, hqm,
      mul_divByMonic_cancel_left]
    exact monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _
  have hinj : Function.Injective (algebraMap A Q) := Subtype.val_injective
  refine ⟨X ^ N /ₘ q, ?_, ?_, ?_⟩
  · apply monic_of_injective hinj
    rw [hg]
    exact monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _
  · rw [← natDegree_map_eq_of_injective hinj, hg]
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum fun l _ => natDegree_X_sub_C_le (x l)).trans ?_
    simp
  · rw [aeval_def, ← eval_map, hg, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_Iic.2 le_rfl) (by simp)

theorem mul_pow_mem (x : Fin N → Q) (j : Fin N) (k : ℕ) (hk : k ≤ (j : ℕ)) {a : Q}
    (ha : a ∈ artinSpan R x ((j : ℕ) + 1)) : a * x j ^ k ∈ artinSpan R x j := by
  classical
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨m, h1, h2, rfl⟩ := h
    refine Submodule.subset_span ⟨m + Pi.single j k, fun i => ?_, fun i hi => ?_, ?_⟩
    · by_cases hij : i = j
      · subst hij
        simp [h2 i (Nat.lt_succ_self _), hk]
      · simp [hij, h1 i]
    · have hij : i ≠ j := by rintro rfl; exact lt_irrefl _ hi
      simp [hij, h2 i (by omega)]
    · simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_eq_single j] <;> simp +contextual
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul r a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha

theorem adjoin_le_artinSpan (x : Fin N → Q) (hx : ∏ l, (X - C (x l)) = (X : Q[X]) ^ N)
    (j : ℕ) (hj : j ≤ N) :
    ∀ a ∈ Algebra.adjoin R (x '' {l | j ≤ (l : ℕ)}), a ∈ artinSpan R x j := by
  classical
  induction hj using Nat.decreasingInduction with
  | self =>
    intro a ha
    have he : x '' {l | N ≤ (l : ℕ)} = ∅ := by
      rw [Set.image_eq_empty, Set.eq_empty_iff_forall_notMem]
      intro l hl
      exact absurd l.2 (not_lt.2 hl)
    rw [he, Algebra.adjoin_empty, Algebra.mem_bot] at ha
    obtain ⟨r, rfl⟩ := ha
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp, by simp, by simp⟩)
  | of_succ j hjN ih =>
    intro a ha
    obtain ⟨g, hg1, hg2, hg3⟩ := exists_monic (R := R) x hx ⟨j, hjN⟩
    have he : x '' {l | j ≤ (l : ℕ)} = x '' {l | j + 1 ≤ (l : ℕ)} ∪ {x ⟨j, hjN⟩} := by
      rw [← Set.image_singleton, ← Set.image_union]
      congr 1
      ext l
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
      omega
    rw [he, Algebra.adjoin_union_eq_adjoin_adjoin, Subalgebra.mem_restrictScalars,
      ← Subalgebra.mem_toSubmodule, ← Submodule.span_range_natDegree_eq_adjoin hg1 hg3] at ha
    have key : ∀ b : Algebra.adjoin R (x '' {l | j + 1 ≤ (l : ℕ)}), b • a ∈ artinSpan R x j := by
      induction ha using Submodule.span_induction with
      | mem a h =>
        intro b
        simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at h
        obtain ⟨k, hk, rfl⟩ := h
        exact mul_pow_mem x ⟨j, hjN⟩ k (by simp only at hg2 ⊢; omega) (ih _ b.2)
      | zero => simp
      | add a c _ _ ha hc => intro b; rw [smul_add]; exact add_mem (ha b) (hc b)
      | smul r a _ ha => intro b; rw [smul_smul]; exact ha _
    simpa using key 1

end General

open MvPolynomial in

theorem artin_monomials_span : ∀ (N : ℕ) (P : MvPolynomial (Fin N) ℝ), ∃ R ∈ Submodule.span ℝ {M : MvPolynomial (Fin N) ℝ | ∃ m : Fin N →₀ ℕ, (∀ i, m i ≤ (i : ℕ)) ∧ M = monomial m 1}, P - R ∈ Ideal.span ((fun k => esymm (Fin N) ℝ k) '' Set.Icc 1 N) := by
  classical
  intro N P
  set I : Ideal (MvPolynomial (Fin N) ℝ) :=
    Ideal.span ((fun k => esymm (Fin N) ℝ k) '' Set.Icc 1 N) with hI
  let π := Ideal.Quotient.mkₐ ℝ I
  let x : Fin N → MvPolynomial (Fin N) ℝ ⧸ I := fun l => π (MvPolynomial.X l)
  have hπ : π = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro l
    simp [x]
  have hes : ∀ k, 1 ≤ k → k ≤ N → (Finset.univ.val.map x).esymm k = 0 := by
    intro k h1 h2
    rw [← aeval_esymm_eq_multiset_esymm (Fin N) ℝ k x, ← hπ]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨k, ⟨h1, h2⟩, rfl⟩)
  have hx : ∏ l, (Polynomial.X - Polynomial.C (x l)) = Polynomial.X ^ N := by
    have h := Multiset.prod_X_sub_X_eq_sum_esymm (Finset.univ.val.map x)
    rw [Multiset.map_map] at h
    refine Eq.trans h ?_
    rw [Finset.sum_eq_single 0]
    · simp [Multiset.esymm]
    · intro k hk hk0
      rw [hes k (by omega) (by simpa [Nat.lt_succ_iff] using hk)]
      simp
    · simp
  have hP : π P ∈ artinSpan ℝ x 0 := by
    apply adjoin_le_artinSpan x hx 0 (Nat.zero_le _)
    have : x '' {l | 0 ≤ (l : ℕ)} = Set.range x := by simp
    rw [this, Algebra.adjoin_range_eq_range_aeval, hπ]
    exact ⟨P, rfl⟩
  have hle : artinSpan ℝ x 0 ≤ (Submodule.span ℝ {M : MvPolynomial (Fin N) ℝ |
      ∃ m : Fin N →₀ ℕ, (∀ i, m i ≤ (i : ℕ)) ∧ M = monomial m 1}).map π.toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨m, h1, -, rfl⟩
    refine ⟨monomial (Finsupp.equivFunOnFinite.symm m) 1,
      Submodule.subset_span ⟨_, fun i => by simpa using h1 i, rfl⟩, ?_⟩
    rw [AlgHom.toLinearMap_apply, hπ, aeval_monomial, map_one, one_mul,
      Finsupp.prod_fintype _ _ (by simp)]
    simp
  obtain ⟨S, hS, hSP⟩ := hle hP
  exact ⟨S, hS, Ideal.Quotient.eq.1 hSP.symm⟩

end GlobalTheory.ArtinSpan
