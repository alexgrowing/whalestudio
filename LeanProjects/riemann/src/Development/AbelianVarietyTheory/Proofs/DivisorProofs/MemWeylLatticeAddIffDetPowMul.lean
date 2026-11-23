import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylRowDivStable

set_option autoImplicit false

noncomputable section

open Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead

namespace GlobalTheory.WeylShift

variable (R : Type) [CommRing R]

theorem rowGen_detPol (n : ℕ) (a b : Fin n) :
    rowGen R a b (detPol R n) =
      (1 + (if a = b then Polynomial.X else 0)) * Polynomial.C (detPol R n) := by
  have hC : (Polynomial.C (detPol R n) : Polynomial (MvPolynomial (Fin n × Fin n) R)) =
      Matrix.det (Matrix.of fun p s : Fin n =>
        (Polynomial.C (X (p, s)) : Polynomial (MvPolynomial (Fin n × Fin n) R))) := by
    unfold detPol
    rw [RingHom.map_det]
    rfl
  rw [hC]
  set A := (Matrix.of fun p s : Fin n =>
        (Polynomial.C (X (p, s)) : Polynomial (MvPolynomial (Fin n × Fin n) R))) with hA
  have h1 : rowGen R a b (detPol R n) =
      Matrix.det (A.updateRow b (A b + (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) R)) • A a)) := by
    unfold detPol
    rw [AlgHom.map_det]
    congr 1
    ext1 p s
    by_cases hp : p = b
    · subst hp
      simp [rowGen, hA]
    · simp [rowGen, hA, hp, Matrix.updateRow_ne hp]
  rw [h1]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, if_pos rfl]
    ring
  · rw [Matrix.det_updateRow_add_smul_self A (Ne.symm hab), if_neg hab]
    ring

theorem rowDiv_det_mul_zero (n : ℕ) (a b : Fin n) (g : MvPolynomial (Fin n × Fin n) R) :
    rowDiv R a b 0 (detPol R n * g) = detPol R n * rowDiv R a b 0 g := by
  unfold rowDiv
  rw [map_mul, rowGen_detPol]
  split_ifs <;> simp [add_mul, mul_assoc]

theorem rowDiv_det_mul_succ (n : ℕ) (a b : Fin n) (j : ℕ) (g : MvPolynomial (Fin n × Fin n) R) :
    rowDiv R a b (j + 1) (detPol R n * g) =
      detPol R n * rowDiv R a b (j + 1) g + (if a = b then detPol R n * rowDiv R a b j g else 0) := by
  unfold rowDiv
  rw [map_mul, rowGen_detPol]
  split_ifs
  · rw [add_mul, add_mul, one_mul, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_X_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  · simp

theorem lpMinor_full (n s : ℕ) (h : s = n) (h1 h2 : s ≤ n) : lpMinor R s h1 h2 = detPol R n := by
  subst h
  rfl

theorem hw_add_one (n : ℕ) (ν : Fin n → ℕ) :
    hw R (le_refl n) (fun a => ν a + 1) = detPol R n * hw R (le_refl n) ν := by
  cases n with
  | zero => simp [hw, detPol]
  | succ m =>
    unfold hw
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    have h1 : ∀ s : Fin m, (ν s.castSucc + 1) - nuNext (fun a => ν a + 1) s.castSucc
        = ν s.castSucc - nuNext ν s.castSucc := by
      intro s
      have hs : s.castSucc.val + 1 < m + 1 := by have := s.2; simp
      simp only [nuNext, dif_pos hs]
      omega
    have h2 : ∀ μ : Fin (m + 1) → ℕ, nuNext μ (Fin.last m) = 0 := by
      intro μ
      simp [nuNext]
    simp only [h1, h2, Nat.sub_zero]
    rw [lpMinor_full R (m + 1) ((Fin.last m).val + 1) (by simp)]
    ring

theorem mem_weyl_add_one (n : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R) :
    f ∈ weyl R n n le_rfl (fun a => ν a + 1) ↔ ∃ g ∈ weyl R n n le_rfl ν, f = detPol R n * g := by
  have key : weyl R n n le_rfl (fun a => ν a + 1) =
      (weyl R n n le_rfl ν).map (LinearMap.mulLeft R (detPol R n)) := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨w, rfl⟩
      induction w with
      | nil =>
        exact ⟨hw R le_rfl ν, Submodule.subset_span ⟨[], rfl⟩, (hw_add_one R n ν).symm⟩
      | cons x w ih =>
        obtain ⟨g, hg, hge⟩ := ih
        obtain ⟨a, b, j⟩ := x
        have he : applyWord R ((a, b, j) :: w) (hw R le_rfl fun a => ν a + 1) =
            rowDiv R a b j (detPol R n * g) := by
          have : detPol R n * g = applyWord R w (hw R le_rfl fun a => ν a + 1) := hge
          rw [this]; rfl
        show applyWord R ((a, b, j) :: w) (hw R le_rfl fun a => ν a + 1) ∈
          (weyl R n n le_rfl ν).map (LinearMap.mulLeft R (detPol R n))
        rw [he]
        have hm : ∀ i, detPol R n * rowDiv R a b i g ∈
            (weyl R n n le_rfl ν).map (LinearMap.mulLeft R (detPol R n)) := fun i =>
          ⟨_, weylModuleRowDividedPowerStable R n n le_rfl ν a b i g hg, rfl⟩
        cases j with
        | zero => rw [rowDiv_det_mul_zero]; exact hm 0
        | succ j =>
          rw [rowDiv_det_mul_succ]
          refine Submodule.add_mem _ (hm _) ?_
          split_ifs
          · exact hm _
          · exact Submodule.zero_mem _
    · rw [Submodule.map_le_iff_le_comap]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨w, rfl⟩
      show detPol R n * applyWord R w (hw R le_rfl ν) ∈ weyl R n n le_rfl (fun a => ν a + 1)
      induction w with
      | nil =>
        exact Submodule.subset_span ⟨[], hw_add_one R n ν⟩
      | cons x w ih =>
        obtain ⟨a, b, j⟩ := x
        show detPol R n * rowDiv R a b j (applyWord R w (hw R le_rfl ν)) ∈ _
        generalize applyWord R w (hw R le_rfl ν) = g at ih ⊢
        have hm : ∀ i, rowDiv R a b i (detPol R n * g) ∈ weyl R n n le_rfl (fun a => ν a + 1) := fun i =>
          weylModuleRowDividedPowerStable R n n le_rfl _ a b i _ ih
        induction j with
        | zero => rw [← rowDiv_det_mul_zero]; exact hm 0
        | succ j ihj =>
          have h := hm (j + 1)
          rw [rowDiv_det_mul_succ] at h
          refine (Submodule.add_mem_iff_left _ ?_).1 h
          split_ifs
          · exact ihj
          · exact Submodule.zero_mem _
  rw [key, Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩

theorem mem_weyl_add (R : Type) [CommRing R] (n k : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R) :
    f ∈ weyl R n n le_rfl (fun a => ν a + k) ↔ ∃ g ∈ weyl R n n le_rfl ν, f = detPol R n ^ k * g := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    have h := mem_weyl_add_one R n (fun a => ν a + k) f
    refine Iff.trans h ?_
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨g', hg', rfl⟩ := (ih g).1 hg
      exact ⟨g', hg', by ring⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨_, (ih _).2 ⟨g, hg, rfl⟩, by ring⟩

end GlobalTheory.WeylShift
