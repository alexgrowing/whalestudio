import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DLiftIdem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DIdemRank
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem fg_ev {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E) (r : ℕ)
    (h : D.D A[X] (1 + X ⊗ₜ e) = (1 + X) ^ r) (b : A[X]) : D.D A[X] (1 + (b - 1) ⊗ₜ e) = b ^ r := by
  have h2 := D.nat A[X] A[X] (aeval (b - 1)) (1 + X ⊗ₜ e)
  rw [h] at h2
  simpa using h2

private theorem fg_chi {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E)
    (he : IsIdempotentElem e) (r s : ℕ) (h : D.D A[X] (1 + X ⊗ₜ e) = (1 + X) ^ r)
    (h' : D.D A[X] (1 + X ⊗ₜ (1 - e)) = (1 + X) ^ s) : D.chi e = X ^ s * (X - 1) ^ r := by
  rw [← fg_ev D e r h, ← fg_ev D (1 - e) s h', ← map_mul, Det.chi]
  congr 1
  rw [add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul, he.one_sub_mul_self, tmul_zero]
  simp only [one_mul, mul_one, tmul_sub, sub_tmul, ← Algebra.TensorProduct.one_def]
  abel

private theorem fg_one {k : Type} [Field k] {r s m : ℕ} (h : (X : k[X]) ^ s * (X - 1) ^ r = (X - 1) * X ^ m) :
    r = 1 := by
  rcases r with _ | _ | r
  · simpa using congrArg (eval 1) h
  · rfl
  · have h0 : (X - 1 : k[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : k)
    rw [pow_succ' _ (r + 1), mul_left_comm] at h
    simpa using congrArg (eval 1) (mul_left_cancel₀ h0 h)

theorem UpperTheory.V.CA.f_gma :
    ∀ {n : ℕ} {B E k : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Ring E] [Algebra B E] [Field k] [Algebra B k] [IsLocalHom (algebraMap B k)] (D : Det n B E) (π : E →ₐ[B] (Fin n → k)), D.IsCH → Function.Surjective π → (∀ x, (D.chi x).map (algebraMap B k) = ∏ i, (X - C (π x i))) → (∀ x, π x = 0 ↔ x ∈ Ring.jacobson E) ∧ ∃ e : Fin n → E, IsGMA D e ∧ ∀ i, π (e i) = Pi.single i 1 := by
  intro n B E k _ _ _ _ _ _ _ _ _ D π hD hs hchi
  obtain ⟨hu, hint⟩ := d_unit D hD
  have hunit : ∀ x, π x = 1 → IsUnit x := by
    intro x hx
    rw [hu, ← (d_chi D x).2.2.2.1, Det.lam, Nat.sub_self]
    refine (isUnit_one.neg.pow n).mul ?_
    refine (isUnit_map_iff (algebraMap B k) _).1 ?_
    rw [← coeff_map, hchi, hx, coeff_zero_eq_eval_zero, isUnit_iff_ne_zero]
    simp [eval_prod]
  have hk : ∀ x, π x = 0 → x ∈ Ring.jacobson E := by
    intro x hx
    rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
    intro y
    obtain ⟨u, hu'⟩ := hunit (y * x + 1) (by simp [hx])
    refine ⟨↑u⁻¹, ?_⟩
    rw [Ideal.mem_bot, sub_eq_zero, ← u.inv_mul, hu', mul_add, mul_one, mul_assoc]
  refine ⟨fun x => ⟨hk x, fun hx => ?_⟩, ?_⟩
  · rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff] at hx
    funext i
    by_contra hi
    obtain ⟨y, hy⟩ := hs fun _ => -(π x i)⁻¹
    obtain ⟨z, hz⟩ := hx y
    rw [Ideal.mem_bot] at hz
    have h1 := congrFun (congrArg π hz) i
    have hi' : π x i ≠ 0 := hi
    simp only [map_sub, map_add, map_mul, map_one, map_zero, hy, Pi.sub_apply, Pi.add_apply, Pi.mul_apply,
      Pi.one_apply, Pi.zero_apply] at h1
    rw [mul_assoc, neg_mul, inv_mul_cancel₀ hi'] at h1
    simp at h1
  · obtain ⟨e, he, he'⟩ := d_lift_idem π hs hk (fun i => Pi.single i 1)
      (CompleteOrthogonalIdempotents.single fun _ : Fin n => k)
    refine ⟨e, ⟨hD, he, fun i => ?_⟩, he'⟩
    obtain ⟨r, -, hr⟩ := d_idem_rank D (e i) (he.idem i)
    obtain ⟨s, -, hs'⟩ := d_idem_rank D (1 - e i) (he.idem i).one_sub
    have h1 := hchi (e i)
    rw [fg_chi D _ (he.idem i) r s hr hs', he', ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      Finset.prod_congr rfl (g := fun _ => X) (fun j hj => by
        simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj)]), Finset.prod_const] at h1
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_X, Polynomial.map_one,
      Pi.single_eq_same, map_one] at h1
    rw [hr, fg_one h1, pow_one]
