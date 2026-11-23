import Mathlib

namespace GlobalTheory

open scoped BigOperators

theorem exists_coord_family_of_finite (X : Type) [AddCommGroup X] [Module.Finite ℤ X] :
    ∃ (n : ℕ) (e : Fin n → X) (c : Fin n → (X →ₗ[ℤ] ℤ)),
      ∀ (f : X →ₗ[ℤ] ℤ) (x : X), f x = ∑ i, c i x * f (e i) := by
  classical
  let T : Submodule ℤ X := Submodule.torsion ℤ X
  haveI : Module.Free ℤ (X ⧸ T) := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ (X ⧸ T)
  have hlift : ∀ i, ∃ x : X, T.mkQ x = b i := fun i => T.mkQ_surjective (b i)
  choose e he using hlift
  refine ⟨_, e, fun i => (b.coord i).comp T.mkQ, fun f x => ?_⟩
  have hmem : x - ∑ i, (b.coord i (T.mkQ x)) • e i ∈ T := by
    apply (Submodule.Quotient.mk_eq_zero T).1
    change T.mkQ _ = 0
    rw [map_sub, map_sum]
    simp only [map_smul, he]
    rw [sub_eq_zero]
    simpa using (b.sum_repr (T.mkQ x)).symm
  have hzero : ∀ t ∈ T, f t = 0 := by
    intro t ht
    obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff t).1 ht
    have h1 : (n : ℤ) • f t = 0 := by
      rw [← map_smul]
      have : (n : ℤ) • t = 0 := hn
      rw [this, map_zero]
    have hn0 : (n : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero n
    exact (smul_eq_zero.1 h1).resolve_left hn0
  have h2 := hzero _ hmem
  rw [map_sub, map_sum, sub_eq_zero] at h2
  rw [h2]
  simp [map_smul]

theorem two_mul_functional_eq_sum_diag (X : Type) [AddCommGroup X] [Module.Finite ℤ X]
    (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    ∃ (m : ℕ) (y : Fin m → X) (a : Fin m → ℤ), ∀ β : LinearMap.BilinForm ℤ X,
      (∀ u v, β u v = β v u) → 2 * ℓ β = ∑ i, a i * β (y i) (y i) := by
  classical
  obtain ⟨n, e, c, hc⟩ := exists_coord_family_of_finite X
  let B : Fin n → Fin n → LinearMap.BilinForm ℤ X := fun i j => (c i).smulRight (c j)
  have hB : ∀ i j x z, B i j x z = c i x * c j z := by
    intro i j x z; simp [B]
  have hexp : ∀ β : LinearMap.BilinForm ℤ X,
      ℓ β = ∑ i, ∑ j, β (e i) (e j) * ℓ (B i j) := by
    intro β
    have hβ : β = ∑ i, ∑ j, β (e i) (e j) • B i j := by
      ext x z
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, hB, smul_eq_mul]
      rw [show β x z = β.flip z x from rfl, hc (β.flip z) x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show β.flip z (e i) = β (e i) z from rfl, hc (β (e i)) z, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    conv_lhs => rw [hβ]
    simp [map_sum, map_smul, smul_eq_mul]
  let ι := (Fin n × Fin n) × Fin 3
  let Y : ι → X := fun p => ![e p.1.1 + e p.1.2, e p.1.1, e p.1.2] p.2
  let A : ι → ℤ := fun p => ![ℓ (B p.1.1 p.1.2), -ℓ (B p.1.1 p.1.2), -ℓ (B p.1.1 p.1.2)] p.2
  have key : ∀ β : LinearMap.BilinForm ℤ X, (∀ u v, β u v = β v u) →
      2 * ℓ β = ∑ p : ι, A p * β (Y p) (Y p) := by
    intro β hs
    rw [hexp β, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.sum_univ_three, Y, A, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_add, LinearMap.add_apply]
    rw [hs (e j) (e i)]
    ring
  let eqv := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun k => Y (eqv.symm k), fun k => A (eqv.symm k), fun β hs => ?_⟩
  rw [key β hs]
  exact (Equiv.sum_comp eqv.symm (fun p => A p * β (Y p) (Y p))).symm

end GlobalTheory
