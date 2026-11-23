import Formalism.GaussJetBounds.GenLogInverse
import Formalism.GaussJetBounds.StatementH

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open MvPolynomial

section ShapeSec

variable {σ : Type}

lemma shape_prod_eq {R : Type u} [CommRing R] {ι : Type*} (g : (σ →₀ ℕ) → ℕ) (hg0 : g 0 = 0)
    (hgadd : ∀ a b, g (a + b) = g a + g b) (f : ι → MvPolynomial σ R) (a : ι → ℕ) (s : Finset ι)
    (h : ∀ c ∈ s, ∀ mono ∈ (f c).support, g mono = a c) :
    ∀ mono ∈ (∏ c ∈ s, f c).support, g mono = ∑ c ∈ s, a c := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro _ mono hm
    rw [Finset.prod_empty, MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    split_ifs at hm with h0
    · rw [← h0, hg0, Finset.sum_empty]
    · exact absurd rfl hm
  | insert c s hc ih =>
    intro h mono hm
    rw [Finset.prod_insert hc] at hm
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
    rw [hgadd, Finset.sum_insert hc, h c (Finset.mem_insert_self c s) m1 hm1,
      ih (fun c' hc' => h c' (Finset.mem_insert_of_mem hc')) m2 hm2]

lemma shape_prod_le {R : Type u} [CommRing R] {ι : Type*} (g : (σ →₀ ℕ) → ℕ) (hg0 : g 0 = 0)
    (hgadd : ∀ a b, g (a + b) = g a + g b) (f : ι → MvPolynomial σ R) (a : ι → ℕ) (s : Finset ι)
    (h : ∀ c ∈ s, ∀ mono ∈ (f c).support, g mono ≤ a c) :
    ∀ mono ∈ (∏ c ∈ s, f c).support, g mono ≤ ∑ c ∈ s, a c := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro _ mono hm
    rw [Finset.prod_empty, MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    split_ifs at hm with h0
    · rw [← h0, hg0, Finset.sum_empty]
    · exact absurd rfl hm
  | insert c s hc ih =>
    intro h mono hm
    rw [Finset.prod_insert hc] at hm
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
    rw [hgadd, Finset.sum_insert hc]
    exact Nat.add_le_add (h c (Finset.mem_insert_self c s) m1 hm1)
      (ih (fun c' hc' => h c' (Finset.mem_insert_of_mem hc')) m2 hm2)

end ShapeSec

lemma shape_count_total {J : Type} [Fintype J] [DecidableEq J] {p : ℕ} (τ : Fin p → J) :
    (∑ j, (Finset.univ.filter (fun i => τ i = j)).card) = p := by
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin p)))
    (t := Finset.univ) (f := τ) (fun i _ => Finset.mem_coe.mpr (Finset.mem_univ (τ i)))
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact this.symm

lemma shape_count_le_one {J : Type} [DecidableEq J] {p : ℕ} (τ : Fin p → J)
    (hτ : Function.Injective τ) (j : J) :
    (Finset.univ.filter (fun i => τ i = j)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact hτ (ha.trans hb.symm)

def shapeSet {R : Type u} [CommRing R] {J : Type} {N1 p : ℕ} (A : Fin p → J → R)
    (I : Fin p → Fin N1) : Set (J × Fin N1 →₀ ℕ) :=
  {mono | ∃ τ : Fin p → J, Function.Injective τ ∧
    (∃ π : Equiv.Perm (Fin p), ∀ i, A (π i) (τ i) ≠ 0) ∧ mono = ∑ i, Finsupp.single (τ i, I i) 1}

lemma shape_minor {R : Type u} [CommRing R] {J : Type} [Fintype J] [DecidableEq J] {N1 p : ℕ}
    (A : Fin p → J → R) (I : Fin p → Fin N1) :
    (Matrix.of fun (r r' : Fin p) =>
      (∑ j, C (A r j) * X (j, I r') : MvPolynomial (J × Fin N1) R)).det ∈
        restrictSupport R (shapeSet A I) := by
  classical
  have hτ : ∀ τ : Fin p → J, ∑ π : Equiv.Perm (Fin p), Equiv.Perm.sign π •
      ∏ i, (C (A (π i) (τ i)) * X (τ i, I i) : MvPolynomial (J × Fin N1) R) =
      C (Matrix.of fun (r i : Fin p) => A r (τ i)).det * ∏ i, X (τ i, I i) := by
    intro τ
    rw [Matrix.det_apply, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun π _ => ?_
    simp only [Units.smul_def, map_zsmul, smul_mul_assoc, Finset.prod_mul_distrib, map_prod,
      Matrix.of_apply]
  rw [Matrix.det_apply]
  simp only [Matrix.of_apply]
  simp_rw [Finset.prod_univ_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Submodule.sum_mem _ fun τ _ => ?_
  have hX : ∏ i, (X (τ i, I i) : MvPolynomial (J × Fin N1) R) =
      monomial (∑ i, Finsupp.single (τ i, I i) 1) 1 := by
    rw [monomial_sum_one]
    rfl
  rw [hτ τ, hX, C_mul_monomial, mul_one, monomial_mem_restrictSupport]
  by_cases hinj : Function.Injective τ
  · by_cases hd : (Matrix.of fun (r i : Fin p) => A r (τ i)).det = 0
    · exact Or.inr hd
    · left
      refine ⟨τ, hinj, ?_, rfl⟩
      by_contra hno
      push_neg at hno
      apply hd
      rw [Matrix.det_apply]
      refine Finset.sum_eq_zero fun π _ => ?_
      obtain ⟨i, hi⟩ := hno π
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), smul_zero]
  · right
    simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, i', hii, hne⟩ := hinj
    exact Matrix.det_zero_of_column_eq hne (fun k => by simp [hii])

lemma shape_minor_mem {R : Type u} [CommRing R] {J : Type} [Fintype J] [DecidableEq J]
    {N1 p : ℕ} (A : Fin p → J → R) (I : Fin p → Fin N1) (mono : J × Fin N1 →₀ ℕ)
    (hm : mono ∈ (Matrix.of fun (r r' : Fin p) =>
      (∑ j, C (A r j) * X (j, I r') : MvPolynomial (J × Fin N1) R)).det.support) :
    mono ∈ shapeSet A I := by
  have h := shape_minor A I
  rw [mem_restrictSupport_iff] at h
  exact h hm

def shapeATop {R : Type u} [CommRing R] {N0 m : ℕ} (T : Fin N0 → Fin m → R) (i : Fin N0) :
    Option (Fin m) → R
  | none => if i.val = 0 then 1 else 0
  | some k => if i.val = 0 then 0 else T i k

end Formalism.DworkPowerSeriesWeights
