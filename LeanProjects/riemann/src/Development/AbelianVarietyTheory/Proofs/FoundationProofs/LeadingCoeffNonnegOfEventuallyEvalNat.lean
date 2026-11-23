import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.XSmulMemWeightedHomogeneousSubmodule

open Polynomial Filter Module

namespace GlobalTheory

attribute [local instance] MvPolynomial.gradedAlgebra

section Poly

theorem polynomial_eq_of_eventually_eval_nat {P Q : ℚ[X]}
    (h : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = Q.eval (n : ℚ)) : P = Q := by
  apply eq_of_infinite_eval_eq
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine Set.Infinite.mono (s := (Nat.cast : ℕ → ℚ) '' Set.Ici N) ?_
    ((Set.Ici_infinite N).image Nat.cast_injective.injOn)
  rintro _ ⟨n, hn, rfl⟩
  exact hN n hn

theorem leadingCoeff_nonneg_of_eventually_eval_nat {P : ℚ[X]}
    (h : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ)) : 0 ≤ P.leadingCoeff := by
  by_contra hneg
  push Not at hneg
  rcases le_or_gt P.degree 0 with h0 | h0
  · obtain ⟨n, hn⟩ := h.exists
    rw [eq_C_of_degree_le_zero h0] at hn hneg
    simp only [eval_C, leadingCoeff_C] at hn hneg
    exact absurd hn (not_le.2 hneg)
  · have := ((tendsto_atBot_of_leadingCoeff_nonpos P h0 hneg.le).comp
      (tendsto_natCast_atTop_atTop (R := ℚ))).eventually (eventually_lt_atBot 0)
    obtain ⟨n, h1, h2⟩ := (h.and this).exists
    exact absurd h1 (not_le.2 h2)

theorem coeff_nonneg_of_eventually_eval_nat {P : ℚ[X]} {e : ℕ} (he : P.degree ≤ e)
    (h : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ)) : 0 ≤ P.coeff e := by
  rcases he.eq_or_lt with he | he
  · rw [← natDegree_eq_of_degree_eq_some he]
    exact leadingCoeff_nonneg_of_eventually_eval_nat h
  · rw [coeff_eq_zero_of_degree_lt he]

theorem degree_le_of_eventually_eval_nat {P Q : ℚ[X]}
    (hP : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ))
    (h : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) : P.degree ≤ Q.degree := by
  by_contra hlt
  push Not at hlt
  have hP0 : P ≠ 0 := by rintro rfl; simp at hlt
  have h1 : 0 ≤ (Q - P).leadingCoeff := leadingCoeff_nonneg_of_eventually_eval_nat (by
    filter_upwards [h] with n hn
    rw [eval_sub]; linarith)
  rw [leadingCoeff_sub_of_degree_lt' hlt] at h1
  have h2 := leadingCoeff_nonneg_of_eventually_eval_nat hP
  exact hP0 (leadingCoeff_eq_zero.1 (by linarith))

theorem exists_int_factorial_mul_coeff {e : ℕ} {P : ℚ[X]} (he : P.degree ≤ e)
    (h : ∀ᶠ n : ℕ in atTop, ∃ z : ℤ, P.eval (n : ℚ) = z) :
    ∃ z : ℤ, (e.factorial : ℚ) * P.coeff e = z := by
  induction e generalizing P with
  | zero =>
    obtain ⟨n, z, hz⟩ := h.exists
    refine ⟨z, ?_⟩
    rw [eq_C_of_degree_le_zero he] at hz
    simpa using hz
  | succ e ih =>
    have h1 := degree_comp_X_add_C_sub_lt P 1 (e + 1) he
    obtain ⟨z, hz⟩ := ih (P := P.comp (X + C 1) - P)
      (degree_le_iff_coeff_zero _ _ |>.2 fun m hm => (degree_lt_iff_coeff_zero _ _).1 h1 m
        (by exact_mod_cast hm)) (by
        filter_upwards [h, (tendsto_add_atTop_nat 1).eventually h] with n ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨b - a, ?_⟩
        simp only [eval_sub, eval_comp, eval_add, eval_X, eval_C]
        push_cast at hb ⊢
        rw [ha, hb])
    refine ⟨z, ?_⟩
    rw [← hz, coeff_comp_X_add_C_sub P 1 e he, Nat.factorial_succ]
    push_cast
    ring

end Poly

open MvPolynomial DirectSum

variable {ι k : Type*} [Field k]

noncomputable def quotPiece (I : Ideal (MvPolynomial ι k)) (n : ℤ) :
    Submodule k (MvPolynomial ι k ⧸ I) :=
  (weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) n).map
    (Ideal.Quotient.mkₐ k I).toLinearMap

theorem weightedHomogeneousSubmodule_one_natCast (n : ℕ) :
    weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) (n : ℤ) =
      homogeneousSubmodule ι k n := by
  ext p
  have : ∀ s : ι →₀ ℕ, Finsupp.weight (fun _ : ι => (1 : ℤ)) s =
      ((Finsupp.weight (1 : ι → ℕ) s : ℕ) : ℤ) := by
    intro s
    simp [Finsupp.weight_apply, Finsupp.sum]
  simp only [mem_weightedHomogeneousSubmodule, mem_homogeneousSubmodule, IsHomogeneous,
    IsWeightedHomogeneous, this, Nat.cast_inj]

theorem quotPiece_natCast (I : Ideal (MvPolynomial ι k)) (n : ℕ) :
    quotPiece I n = (homogeneousSubmodule ι k n).map (Ideal.Quotient.mkₐ k I).toLinearMap := by
  rw [quotPiece, weightedHomogeneousSubmodule_one_natCast]

theorem weightedHomogeneousComponent_one_mem {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) (n : ℤ) {p : MvPolynomial ι k}
    (hp : p ∈ I) : weightedHomogeneousComponent (fun _ : ι => (1 : ℤ)) n p ∈ I := by
  classical
  rw [← sum_homogeneousComponent p, map_sum]
  refine I.sum_mem fun i _ => ?_
  have h1 : homogeneousComponent i p ∈ weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ))
      (i : ℤ) := by
    rw [weightedHomogeneousSubmodule_one_natCast]
    exact homogeneousComponent_mem i p
  rw [weightedHomogeneousComponent_of_mem h1]
  split_ifs
  · have := hI i hp
    rwa [show (decompose (homogeneousSubmodule ι k) p i : MvPolynomial ι k) =
      homogeneousComponent i p from decomposition.decompose'_apply p i] at this
  · exact I.zero_mem

instance finite_homogeneousSubmodule' [Finite ι] (n : ℕ) :
    Module.Finite k (homogeneousSubmodule ι k n) := by
  letI := weightedDecomposition k (fun _ : ι => (1 : ℤ))
  rw [← weightedHomogeneousSubmodule_one_natCast]
  exact GradedHilbert.finite_piece _ (X_smul_mem_weightedHomogeneousSubmodule ι k) _

theorem exists_isHilbertPoly_quotPiece [Fintype ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    ∃ P : ℚ[X], IsHilbertPoly (quotPiece I) P ∧ P.degree < (Fintype.card ι : ℕ) := by
  letI := weightedDecomposition k (fun _ : ι => (1 : ℤ))
  have hfin := GradedHilbert.finite_piece _ (X_smul_mem_weightedHomogeneousSubmodule ι k)
  obtain ⟨P, hP, h⟩ := GradedHilbert.exists_polynomial_subquotient _
    (X_smul_mem_weightedHomogeneousSubmodule ι k) Finset.univ I ⊤ le_top
    (by
      intro n m hm
      have := weightedHomogeneousComponent_one_mem hI n hm
      rwa [← weightedDecomposition.decompose'_apply] at this) (by simp) (by simp)
  refine ⟨P, ⟨fun n => ?_, ?_⟩, hP⟩
  · haveI := hfin n
    unfold quotPiece
    infer_instance
  · filter_upwards [h] with n hn
    haveI := hfin n
    have e := GradedHilbert.finrank_map_add_finrank_inf_ker (Ideal.Quotient.mkₐ k I).toLinearMap
      (weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) n)
    have e2 : LinearMap.ker (Ideal.Quotient.mkₐ k I).toLinearMap = I.restrictScalars k := by
      ext x; simp [Ideal.Quotient.eq_zero_iff_mem]
    rw [e2, inf_comm] at e
    rw [Submodule.restrictScalars_top, top_inf_eq, ← e] at hn
    rw [← hn, quotPiece]
    push_cast
    ring

open Classical in

noncomputable def idealHilbertPoly (I : Ideal (MvPolynomial ι k)) : ℚ[X] :=
  if h : ∃ P, IsHilbertPoly (quotPiece I) P then h.choose else 0

theorem isHilbertPoly_idealHilbertPoly [Finite ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    IsHilbertPoly (quotPiece I) (idealHilbertPoly I) := by
  cases nonempty_fintype ι
  have h : ∃ P, IsHilbertPoly (quotPiece I) P :=
    (exists_isHilbertPoly_quotPiece hI).imp fun _ h => h.1
  rw [idealHilbertPoly, dif_pos h]
  exact h.choose_spec

theorem IsHilbertPoly.idealHilbertPoly_eq {I : Ideal (MvPolynomial ι k)} {P : ℚ[X]}
    (hP : IsHilbertPoly (quotPiece I) P) : idealHilbertPoly I = P := by
  have h : ∃ P, IsHilbertPoly (quotPiece I) P := ⟨P, hP⟩
  rw [idealHilbertPoly, dif_pos h]
  exact h.choose_spec.unique hP

theorem eventually_finrank_quotPiece [Finite ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    ∀ᶠ n : ℕ in atTop, (finrank k (quotPiece I n) : ℚ) = (idealHilbertPoly I).eval (n : ℚ) := by
  have := (tendsto_natCast_atTop_atTop (R := ℤ)).eventually
    (isHilbertPoly_idealHilbertPoly hI).eventually_eq
  simpa using this

theorem finrank_quotPiece_add [Finite ι] (I : Ideal (MvPolynomial ι k)) (n : ℕ) :
    finrank k (quotPiece I n) +
      finrank k (I.restrictScalars k ⊓ homogeneousSubmodule ι k n : Submodule k _) =
      finrank k (homogeneousSubmodule ι k n) := by
  have e := GradedHilbert.finrank_map_add_finrank_inf_ker (Ideal.Quotient.mkₐ k I).toLinearMap
    (homogeneousSubmodule ι k n)
  have e2 : LinearMap.ker (Ideal.Quotient.mkₐ k I).toLinearMap = I.restrictScalars k := by
    ext x; simp [Ideal.Quotient.eq_zero_iff_mem]
  rw [e2, inf_comm] at e
  rw [quotPiece_natCast, e]

theorem eventually_idealHilbertPoly_nonneg [Finite ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ (idealHilbertPoly I).eval (n : ℚ) := by
  filter_upwards [eventually_finrank_quotPiece hI] with n hn
  rw [← hn]
  positivity

noncomputable def hilbertDegree (I : Ideal (MvPolynomial ι k)) : ℕ :=
  ⌊((idealHilbertPoly I).natDegree.factorial : ℚ) * (idealHilbertPoly I).leadingCoeff⌋₊

theorem cast_hilbertDegree [Finite ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    (hilbertDegree I : ℚ) =
      ((idealHilbertPoly I).natDegree.factorial : ℚ) * (idealHilbertPoly I).leadingCoeff := by
  obtain ⟨z, hz⟩ := exists_int_factorial_mul_coeff (P := idealHilbertPoly I)
    degree_le_natDegree (by
      filter_upwards [eventually_finrank_quotPiece hI] with n hn
      exact ⟨finrank k (quotPiece I n), by rw [← hn]; simp⟩)
  have h0 : 0 ≤ ((idealHilbertPoly I).natDegree.factorial : ℚ) *
      (idealHilbertPoly I).leadingCoeff := mul_nonneg (by positivity)
    (leadingCoeff_nonneg_of_eventually_eval_nat (eventually_idealHilbertPoly_nonneg hI))
  rw [hilbertDegree, leadingCoeff, hz]
  rw [leadingCoeff, hz] at h0
  lift z to ℕ using (by exact_mod_cast h0)
  simp

theorem cast_hilbertDegree_of_degree_eq [Finite ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {e : ℕ}
    (he : (idealHilbertPoly I).degree = e) :
    (hilbertDegree I : ℚ) = (e.factorial : ℚ) * (idealHilbertPoly I).coeff e := by
  rw [cast_hilbertDegree hI, leadingCoeff, natDegree_eq_of_degree_eq_some he]

theorem hilbertDegree_eq_zero_iff [Finite ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    hilbertDegree I = 0 ↔ idealHilbertPoly I = 0 := by
  rw [← Nat.cast_eq_zero (R := ℚ), cast_hilbertDegree hI, mul_eq_zero, leadingCoeff_eq_zero]
  simp [Nat.factorial_ne_zero]

def projComponents (I : Ideal (MvPolynomial ι k)) : Set (Ideal (MvPolynomial ι k)) :=
  {P | P ∈ I.minimalPrimes ∧ ∃ i, (X i : MvPolynomial ι k) ∉ P}

theorem finite_projComponents [Finite ι] (I : Ideal (MvPolynomial ι k)) :
    (projComponents I).Finite :=
  I.finite_minimalPrimes_of_isNoetherianRing.subset fun _ h => h.1

noncomputable def projSetDegree [Finite ι] (I : Ideal (MvPolynomial ι k)) : ℕ :=
  ∑ P ∈ (finite_projComponents I).toFinset, hilbertDegree P

def IsProjPureDim (I : Ideal (MvPolynomial ι k)) (e : ℕ) : Prop :=
  ∀ P ∈ projComponents I, ringKrullDim (MvPolynomial ι k ⧸ P) = (e + 1 : ℕ)

def projPoints (I : Ideal (MvPolynomial ι k)) : Set (Projectivization k (ι → k)) :=
  {y | ∀ g ∈ I, MvPolynomial.eval y.rep g = 0}

end GlobalTheory
