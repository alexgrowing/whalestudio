import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep
import Formalism.SatakeDualWeyl.Statement
import Formalism.FormalDegreeBessel.StatementG
open Matrix
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.DefiniteUnitaryCasimir

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.UnitaryLieComplexification

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ}

theorem exists_linear_extension (hJ : Jᴴ = J) (hu : IsUnit J.det) {A : Type} [Ring A] [Algebra ℂ A] (ρ : lieU J → A)
    (hadd : ∀ X Y, ρ (X + Y) = ρ X + ρ Y) (hsm : ∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A,
      (∀ Z, R Z = ρ (rePart hJ hu Z) + Complex.I • ρ (imPart hJ hu Z)) ∧ (∀ X : lieU J, R X.1 = ρ X) := by
  have hsub : ∀ X Y, ρ (X - Y) = ρ X - ρ Y := by
    intro X Y
    have := hadd (X - Y) Y
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  have h0 : ρ 0 = 0 := by
    have := hsub 0 0
    rwa [sub_self, sub_self] at this
  let r : Matrix (Fin n) (Fin n) ℂ → A := fun Z => ρ (rePart hJ hu Z) + Complex.I • ρ (imPart hJ hu Z)
  have key : ∀ X Y : lieU J, r (X.1 + Complex.I • Y.1) = ρ X + Complex.I • ρ Y := by
    intro X Y
    simp only [r, rePart_mk, imPart_mk]
  have hII : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (m : M), Complex.I • Complex.I • m = -m := by
    intro M _ _ m
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  refine ⟨{ toFun := r, map_add' := ?_, map_smul' := ?_ }, fun Z => rfl, ?_⟩
  · intro Z W
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    obtain ⟨X', Y', rfl⟩ := exists_mk hJ hu W
    have : X.1 + Complex.I • Y.1 + (X'.1 + Complex.I • Y'.1) = (X + X').1 + Complex.I • (Y + Y').1 := by
      change _ = (X.1 + X'.1) + Complex.I • (Y.1 + Y'.1)
      module
    rw [this, key, key, key, hadd, hadd]
    module
  · intro c Z
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    generalize c.re = a at hc
    generalize c.im = b at hc
    subst hc
    have : ((a : ℂ) + (b : ℂ) * Complex.I) • (X.1 + Complex.I • Y.1) =
        (a • X - b • Y).1 + Complex.I • (b • X + a • Y).1 := by
      change _ = ((a : ℂ) • X.1 - (b : ℂ) • Y.1) + Complex.I • ((b : ℂ) • X.1 + (a : ℂ) • Y.1)
      simp only [add_smul, smul_add, mul_smul, hII]
      module
    rw [this, key, key, hsub, hadd, hsm, hsm, hsm, hsm]
    simp only [RingHom.id_apply, add_smul, smul_add, mul_smul, hII]
    module
  · intro X
    have := key X 0
    simpa [h0] using this

theorem mul_single_mul (U V : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    U * single a b (1 : ℂ) * V = ∑ c, ∑ d, (U c a * V b d) • single c d (1 : ℂ) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single (U * single a b (1 : ℂ) * V)]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.smul_single, smul_eq_mul, mul_one]
  congr 1
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem casimir_move {A : Type} [Ring A] [Algebra ℂ A] (R R' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A)
    (U V : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, ∑ b, R (U * single a b 1 * V) * R' (single b a 1) =
      ∑ c, ∑ d, R (single c d 1) * R' (V * single d c 1 * U) := by
  simp only [mul_single_mul, map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type' (f := fun c d => ∑ b, ∑ a, (V b d * U c a) • (R (single c d 1) * R' (single b a 1)))]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _))) _ _
    fun q => ?_
  simp [mul_comm]

theorem casimir_conj {A : Type} [Ring A] [Algebra ℂ A] (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A)
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det) :
    ∑ a, ∑ b, R (single a b 1) * R (single b a 1) =
      ∑ a, ∑ b, R (B⁻¹ * single a b 1 * B) * R (B⁻¹ * single b a 1 * B) := by
  have := casimir_move R (R ∘ₗ (LinearMap.mulRight ℂ B) ∘ₗ (LinearMap.mulLeft ℂ B⁻¹)) B⁻¹ B
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply] at this
  rw [this]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul B hB, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul B hB, Matrix.mul_one]

theorem cj_conj_single (B : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det) (h : J = Bᴴ * B ∨ J = -(Bᴴ * B))
    (a b : Fin n) : cj J (B⁻¹ * single a b 1 * B) = -(B⁻¹ * single b a 1 * B) := by
  have hBH : IsUnit Bᴴ.det := by rw [det_conjTranspose]; exact hB.star
  have key : (Bᴴ * B)⁻¹ * (B⁻¹ * single a b (1 : ℂ) * B)ᴴ * (Bᴴ * B) = B⁻¹ * single b a 1 * B := by
    rw [Matrix.mul_inv_rev, conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv, conjTranspose_single,
      star_one]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᴴ⁻¹ Bᴴ B, ← Matrix.mul_assoc Bᴴ⁻¹ Bᴴ, Matrix.nonsing_inv_mul _ hBH, Matrix.one_mul,
      Matrix.one_mul]
  rcases h with rfl | rfl
  · rw [cj, key]
  · have hu : IsUnit (Bᴴ * B).det := by rw [det_mul]; exact hBH.mul hB
    have : (-(Bᴴ * B))⁻¹ = -(Bᴴ * B)⁻¹ := by
      apply Matrix.inv_eq_left_inv
      rw [neg_mul_neg, Matrix.nonsing_inv_mul _ hu]
    rw [cj, this, neg_mul, neg_mul_neg, key]

theorem sum_squares {A : Type} [Ring A] [Algebra ℂ A] (F : Fin n → Fin n → A) :
    ∑ a, ∑ b, F a b * F b a =
      -∑ a, ∑ b, (((1 / 2 : ℂ) • (F a b - F b a)) * ((1 / 2 : ℂ) • (F a b - F b a)) +
        ((1 / (2 * Complex.I) : ℂ) • (F a b + F b a)) * ((1 / (2 * Complex.I) : ℂ) • (F a b + F b a))) := by
  have h : (1 / (2 * Complex.I) : ℂ) * (1 / (2 * Complex.I)) = -(1 / 4) := by
    field_simp
    simp
    norm_num
  have h1 : ∀ a b, ((1 / 2 : ℂ) • (F a b - F b a)) * ((1 / 2 : ℂ) • (F a b - F b a)) +
        ((1 / (2 * Complex.I) : ℂ) • (F a b + F b a)) * ((1 / (2 * Complex.I) : ℂ) • (F a b + F b a)) =
        -((1 / 2 : ℂ) • (F a b * F b a) + (1 / 2 : ℂ) • (F b a * F a b)) := by
    intro a b
    simp only [smul_mul_smul_comm, h, mul_add, add_mul, mul_sub, sub_mul]
    module
  simp only [h1, Finset.sum_neg_distrib, neg_neg, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [Finset.sum_comm (f := fun a b => F b a * F a b)]
  module

theorem casimir_eq_neg_sum_sq : ∀ (n : ℕ) (J B : Matrix (Fin n) (Fin n) ℂ), IsUnit B.det → (J = Bᴴ * B ∨ J = -(Bᴴ * B)) → ∃ X : Fin n × Fin n × Bool → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Submodule.span ℝ (Set.range X) = ⊤ ∧ ∀ P Q : Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, (∀ a b, (P a b).1 = (1 / 2 : ℂ) • (Matrix.single a b 1 + -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J)) ∧ (Q a b).1 = (1 / (2 * Complex.I)) • (Matrix.single a b 1 - -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J))) → ∀ (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ Y Z, ρ (Y + Z) = ρ Y + ρ Z) → (∀ (c : ℝ) Y, ρ (c • Y) = (c : ℂ) • ρ Y) → ∑ a, ∑ b, (ρ (P a b) + Complex.I • ρ (Q a b)) * (ρ (P b a) + Complex.I • ρ (Q b a)) = -∑ i, ρ (X i) * ρ (X i) := by
  intro n J B hB h
  have hBH : IsUnit Bᴴ.det := by rw [det_conjTranspose]; exact hB.star
  have hJ : Jᴴ = J := by
    rcases h with rfl | rfl <;> simp
  have hu : IsUnit J.det := by
    rcases h with rfl | rfl
    · rw [det_mul]; exact hBH.mul hB
    · rw [det_neg, det_mul]; exact (isUnit_one.neg.pow _).mul (hBH.mul hB)
  let F : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ := fun a b => B⁻¹ * single a b 1 * B
  let X : Fin n × Fin n × Bool → lieU J := fun p =>
    if p.2.2 then rePart hJ hu (F p.1 p.2.1) else imPart hJ hu (F p.1 p.2.1)
  refine ⟨X, ?_, ?_⟩
  · rw [eq_top_iff]
    rintro Y -
    let S : Submodule ℝ (lieU J) := Submodule.span ℝ (Set.range X)
    have hS : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Z ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => F p.1 p.2) →
        ∃ U ∈ S, ∃ V ∈ S, Z = U.1 + Complex.I • V.1 := by
      intro Z hZ
      induction hZ using Submodule.span_induction with
      | mem Z hZ =>
        obtain ⟨⟨a, b⟩, rfl⟩ := hZ
        exact ⟨_, Submodule.subset_span ⟨(a, b, true), rfl⟩, _, Submodule.subset_span ⟨(a, b, false), rfl⟩,
          (re_add_im hJ hu _).symm⟩
      | zero => exact ⟨0, S.zero_mem, 0, S.zero_mem, by simp⟩
      | add Z W _ _ hZ hW =>
        obtain ⟨U, hU, V, hV, rfl⟩ := hZ
        obtain ⟨U', hU', V', hV', rfl⟩ := hW
        refine ⟨U + U', S.add_mem hU hU', V + V', S.add_mem hV hV', ?_⟩
        change _ = (U.1 + U'.1) + Complex.I • (V.1 + V'.1)
        module
      | smul c Z _ hZ =>
        obtain ⟨U, hU, V, hV, rfl⟩ := hZ
        have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
        generalize c.re = a at hc
        generalize c.im = b at hc
        subst hc
        refine ⟨a • U - b • V, S.sub_mem (S.smul_mem _ hU) (S.smul_mem _ hV), b • U + a • V,
          S.add_mem (S.smul_mem _ hU) (S.smul_mem _ hV), ?_⟩
        have hII : ∀ (m : Matrix (Fin n) (Fin n) ℂ), Complex.I • Complex.I • m = -m := by
          intro m
          rw [smul_smul, Complex.I_mul_I, neg_one_smul]
        change _ = ((a : ℂ) • U.1 - (b : ℂ) • V.1) + Complex.I • ((b : ℂ) • U.1 + (a : ℂ) • V.1)
        simp only [add_smul, smul_add, mul_smul, hII]
        module
    have hY : Y.1 ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => F p.1 p.2) := by
      have : Y.1 = B⁻¹ * (B * Y.1 * B⁻¹) * B := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul B hB, Matrix.one_mul, Matrix.mul_assoc,
          Matrix.nonsing_inv_mul B hB, Matrix.mul_one]
      rw [this, Matrix.matrix_eq_sum_single (B * Y.1 * B⁻¹)]
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      have : Matrix.single a b ((B * Y.1 * B⁻¹) a b) = (B * Y.1 * B⁻¹) a b • Matrix.single a b (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [this, mul_smul_comm, smul_mul_assoc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b), rfl⟩)
    obtain ⟨U, hU, V, -, hUV⟩ := hS _ hY
    have h1 := rePart_mk hJ hu U V
    have h2 := rePart_mk hJ hu Y 0
    have h3 : Y.1 + Complex.I • (0 : lieU J).1 = Y.1 := by simp
    rw [h3, hUV, h1] at h2
    rw [← h2]
    exact hU
  · intro P Q hPQ A _ _ ρ hadd hsm
    obtain ⟨R, hR, hX⟩ := exists_linear_extension hJ hu ρ hadd hsm
    have hP : ∀ a b, P a b = rePart hJ hu (single a b 1) := fun a b => Subtype.ext (hPQ a b).1
    have hQ : ∀ a b, Q a b = imPart hJ hu (single a b 1) := fun a b => Subtype.ext (hPQ a b).2
    simp only [hP, hQ, ← hR]
    rw [casimir_conj R B hB, sum_squares (fun a b => R (F a b))]
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e1 : ρ (X (a, b, true)) = (1 / 2 : ℂ) • (R (F a b) - R (F b a)) := by
      rw [← hX]
      change R ((1 / 2 : ℂ) • (F a b + cj J (F a b))) = _
      rw [cj_conj_single B hB h, map_smul, map_add, map_neg, ← sub_eq_add_neg]
    have e2 : ρ (X (a, b, false)) = (1 / (2 * Complex.I) : ℂ) • (R (F a b) + R (F b a)) := by
      rw [← hX]
      change R ((1 / (2 * Complex.I) : ℂ) • (F a b - cj J (F a b))) = _
      rw [cj_conj_single B hB h, map_smul, map_sub, map_neg, sub_neg_eq_add]
    rw [Fintype.sum_bool, e1, e2]

end GlobalTheory.DefiniteUnitaryCasimir
