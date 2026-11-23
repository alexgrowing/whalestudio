import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsLimitOfApprox

namespace GroundTheory.LocalField.FormalGroup

open IsLocalRing

section Approximation

variable {R : Type*} [CommRing R] (I : Ideal R)

theorem smodEq_pow_iff_sub_mem {x y : R} {n : ℕ} :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem exists_limit_of_approx [IsPrecomplete I R] (P : ℕ → R → Prop)
    (hstep : ∀ n x, P n x → ∃ y, y - x ∈ I ^ n ∧ P (n + 1) y) {x₀ : R} (h₀ : P 0 x₀) :
    ∃ x, ∀ n, ∃ y, P n y ∧ x - y ∈ I ^ n :=
  by apply _root_.UpperTheory.Reformulated.B.Qp1.exists_limit_of_approx <;> assumption

theorem exists_eq_zero_of_approx [IsAdicComplete I R] (F : R → R)
    (hF : ∀ n x y, x - y ∈ I ^ n → F x - F y ∈ I ^ n)
    (hstep : ∀ n x, F x ∈ I ^ n → ∃ y, y - x ∈ I ^ n ∧ F y ∈ I ^ (n + 1))
    {m : ℕ} {x₀ : R} (h₀ : F x₀ ∈ I ^ m) : ∃ x, F x = 0 ∧ x - x₀ ∈ I ^ m := by
  obtain ⟨x, hx⟩ := exists_limit_of_approx I (fun n y => F y ∈ I ^ (m + n) ∧ y - x₀ ∈ I ^ m)
    (fun n y ⟨h1, h2⟩ => by
      obtain ⟨z, hz1, hz2⟩ := hstep (m + n) y h1
      refine ⟨z, Ideal.pow_le_pow_right (by omega) hz1, hz2, ?_⟩
      have e : z - x₀ = (z - y) + (y - x₀) := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) hz1) h2)
    ⟨by simpa using h₀, by simp⟩
  refine ⟨x, ?_, ?_⟩
  · refine IsHausdorff.haus (I := I) inferInstance _ fun n => ?_
    rw [smodEq_pow_iff_sub_mem, sub_zero]
    obtain ⟨y, ⟨hy1, _⟩, hy⟩ := hx n
    have e : F x = (F x - F y) + F y := by ring
    rw [e]
    exact Ideal.add_mem _ (hF n x y hy) (Ideal.pow_le_pow_right (by omega) hy1)
  · obtain ⟨y, ⟨_, hy2⟩, hy⟩ := hx m
    have e : x - x₀ = (x - y) + (y - x₀) := by ring
    rw [e]
    exact Ideal.add_mem _ hy hy2

end Approximation

section HidaSetting

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]

theorem isLocalHom_of_map_maximalIdeal
    (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    IsLocalHom (algebraMap A B) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have hm : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 h
  have := Ideal.mem_map_of_mem (algebraMap A B) hm
  rw [hunr] at this
  exact (mem_maximalIdeal _).1 this ha

theorem irreducible_algebraMap (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    {π : A} (hπ : Irreducible π) : Irreducible (algebraMap A B π) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hπ ⊢
  rw [← hunr, hπ, Ideal.map_span, Set.image_singleton]

theorem mem_maximalIdeal_pow_iff {ϖ : B} (hϖ : Irreducible ϖ) {x : B} {n : ℕ} :
    x ∈ maximalIdeal B ^ n ↔ ϖ ^ n ∣ x := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

end HidaSetting

section Solve

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [Finite (ResidueField A)] [IsAlgClosed (ResidueField B)]
  (σ : B →ₐ[A] B)
  (hσ : ∀ x : B, residue B (σ x) = residue B x ^ Nat.card (ResidueField A))

theorem one_lt_card_residueField : 1 < Nat.card (ResidueField A) :=
  Finite.one_lt_card

include hσ in

theorem exists_residue_sub_mul_add_eq_zero (v w : B) :
    ∃ z : B, residue B (σ z - v * z + w) = 0 := by
  open Polynomial in
  set q := Nat.card (ResidueField A)
  have hq : 1 < q := one_lt_card_residueField
  set a := residue B v
  set b := residue B w
  have hlow : (C b - C a * X : (ResidueField B)[X]).degree < (X ^ q : (ResidueField B)[X]).degree := by
    rw [degree_X_pow]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast (by omega : 0 < q))
    · exact lt_of_le_of_lt (degree_C_mul_X_le a) (by exact_mod_cast hq)
  have hdeg : (X ^ q + (C b - C a * X) : (ResidueField B)[X]).degree = q := by
    rw [degree_add_eq_left_of_degree_lt hlow, degree_X_pow]
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (X ^ q + (C b - C a * X) : (ResidueField B)[X])
    (by rw [hdeg]; exact_mod_cast (by omega : q ≠ 0))
  obtain ⟨z', rfl⟩ := residue_surjective z
  refine ⟨z', ?_⟩
  simp only [IsRoot, eval_add, eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hz
  rw [map_add, map_sub, map_mul, hσ]
  linear_combination hz

variable {π : A} (hπB : Irreducible (algebraMap A B π))
include hσ hπB

theorem exists_sub_mul_eq_of_mem [IsAdicComplete (maximalIdeal B) B] (v c : B) {m : ℕ} {x₀ : B}
    (h₀ : σ x₀ - v * x₀ - c ∈ maximalIdeal B ^ m) :
    ∃ x, σ x - v * x = c ∧ x - x₀ ∈ maximalIdeal B ^ m := by
  set ϖ := algebraMap A B π
  have hσϖ : ∀ (n : ℕ) (t : B), σ (ϖ ^ n * t) = ϖ ^ n * σ t := by
    intro n t
    rw [map_mul, map_pow, AlgHom.commutes]
  obtain ⟨x, hx, hxm⟩ := exists_eq_zero_of_approx (maximalIdeal B) (fun x => σ x - v * x - c)
    (fun n x y hxy => by
      rw [mem_maximalIdeal_pow_iff hπB] at hxy ⊢
      obtain ⟨t, ht⟩ := hxy
      refine ⟨σ t - v * t, ?_⟩
      have : x = y + ϖ ^ n * t := by rw [← ht]; ring
      simp only [this, map_add, hσϖ]
      ring)
    (fun n x hx => by
      rw [mem_maximalIdeal_pow_iff hπB] at hx
      obtain ⟨w, hw⟩ := hx
      obtain ⟨z, hz⟩ := exists_residue_sub_mul_add_eq_zero σ hσ v w
      rw [residue_eq_zero_iff, hπB.maximalIdeal_eq, Ideal.mem_span_singleton] at hz
      obtain ⟨t, ht⟩ := hz
      refine ⟨x + ϖ ^ n * z, ?_, ?_⟩
      · rw [mem_maximalIdeal_pow_iff hπB]
        exact ⟨z, by ring⟩
      · rw [mem_maximalIdeal_pow_iff hπB]
        refine ⟨t, ?_⟩
        simp only [map_add, hσϖ]
        have e : σ x - v * x - c = ϖ ^ n * w := hw
        linear_combination e + ϖ ^ n * ht)
    h₀
  exact ⟨x, sub_eq_zero.1 (by simpa using hx), hxm⟩

theorem exists_sub_mul_eq [IsAdicComplete (maximalIdeal B) B] (v c : B) :
    ∃ x, σ x - v * x = c := by
  obtain ⟨x, hx, -⟩ := exists_sub_mul_eq_of_mem σ hσ hπB v c (m := 0) (x₀ := 0) (by simp)
  exact ⟨x, hx⟩

theorem exists_units_eq_mul [IsAdicComplete (maximalIdeal B) B] (v : Bˣ) :
    ∃ η : Bˣ, σ η = v * η := by
  set q := Nat.card (ResidueField A)
  have hq : 1 < q := one_lt_card_residueField
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (residue B v) (n := q - 1) (by omega)
  have hv0 : residue B v ≠ 0 := (residue_ne_zero_iff_isUnit _).2 v.isUnit
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hz
    exact hv0 hz.symm
  obtain ⟨z', rfl⟩ := residue_surjective z
  have h₀ : σ z' - v * z' - 0 ∈ maximalIdeal B ^ 1 := by
    rw [pow_one, ← residue_eq_zero_iff, sub_zero, map_sub, map_mul, hσ]
    have e : residue B z' ^ q = residue B z' ^ (q - 1) * residue B z' := by
      rw [← pow_succ]; congr 1; omega
    rw [e, hz, sub_self]
  obtain ⟨x, hx, hxm⟩ := exists_sub_mul_eq_of_mem σ hσ hπB v 0 h₀
  have hxu : IsUnit x := by
    rw [← residue_ne_zero_iff_isUnit]
    rw [pow_one, ← residue_eq_zero_iff, map_sub, sub_eq_zero] at hxm
    rwa [hxm]
  refine ⟨hxu.unit, ?_⟩
  simpa [sub_eq_zero] using hx

end Solve

section Kernel

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [Finite (ResidueField A)] [IsAlgClosed (ResidueField B)] [IsAdicComplete (maximalIdeal B) B]
  (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
  (σ : B →ₐ[A] B)
  (hσ : ∀ x : B, residue B (σ x) = residue B x ^ Nat.card (ResidueField A))

include hunr hσ

theorem surjective_sub_self : Function.Surjective fun x : B => σ x - x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  intro c
  obtain ⟨x, hx⟩ := exists_sub_mul_eq σ hσ (irreducible_algebraMap hunr hπ) 1 c
  exact ⟨x, by simpa using hx⟩

theorem surjective_div_self :
    Function.Surjective fun u : Bˣ => Units.map (σ : B →* B) u / u := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  intro v
  obtain ⟨η, hη⟩ := exists_units_eq_mul σ hσ (irreducible_algebraMap hunr hπ) v
  refine ⟨η, ?_⟩
  rw [div_eq_iff_eq_mul]
  ext
  simpa using hη
