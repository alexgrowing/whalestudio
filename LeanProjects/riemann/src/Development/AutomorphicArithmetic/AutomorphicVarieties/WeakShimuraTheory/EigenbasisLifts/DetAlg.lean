import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.MatrixUnits2
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DLiftIdem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DIdemRank
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DCorner
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmaDet

section

open TensorProduct Polynomial UpperTheory.V.W UpperTheory.V.CA

private theorem da_ev {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E) (r : ℕ)
    (h : D.D A[X] (1 + X ⊗ₜ e) = (1 + X) ^ r) (b : A[X]) : D.D A[X] (1 + (b - 1) ⊗ₜ e) = b ^ r := by
  have h2 := D.nat A[X] A[X] (aeval (b - 1)) (1 + X ⊗ₜ e)
  rw [h] at h2
  simpa using h2

private theorem da_chi {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E)
    (he : IsIdempotentElem e) (r s : ℕ) (h : D.D A[X] (1 + X ⊗ₜ e) = (1 + X) ^ r)
    (h' : D.D A[X] (1 + X ⊗ₜ (1 - e)) = (1 + X) ^ s) : D.chi e = X ^ s * (X - 1) ^ r := by
  rw [← da_ev D e r h, ← da_ev D (1 - e) s h', ← map_mul, Det.chi]
  congr 1
  rw [add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul, he.one_sub_mul_self, tmul_zero]
  simp only [one_mul, mul_one, tmul_sub, sub_tmul, ← Algebra.TensorProduct.one_def]
  abel

private theorem da_one {k : Type} [Field k] {r s m : ℕ} (h : (X : k[X]) ^ s * (X - 1) ^ r = (X - 1) * X ^ m) :
    r = 1 := by
  rcases r with _ | _ | r
  · simpa using congrArg (eval 1) h
  · rfl
  · have h0 : (X - 1 : k[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : k)
    rw [pow_succ' _ (r + 1), mul_left_comm] at h
    simpa using congrArg (eval 1) (mul_left_cancel₀ h0 h)

private theorem da_single {k : Type} [Field k] {n : ℕ} (i : Fin n) :
    ∃ m, (Matrix.single i i (1 : k)).charpoly = (X - 1) * X ^ m := by
  refine ⟨(Finset.univ.erase i).card, ?_⟩
  rw [← Matrix.diagonal_single, Matrix.charpoly_diagonal, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      Finset.prod_congr rfl (g := fun _ => X) (fun j hj => by
        simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj)]), Finset.prod_const]
  simp

private theorem da_coi {k : Type} [Field k] {n : ℕ} :
    CompleteOrthogonalIdempotents (fun i : Fin n => Matrix.single i i (1 : k)) := by
  refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
  · simp [IsIdempotentElem]
  · simp [hij]
  · exact Matrix.sum_single_one

end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.detAlg :
    ∀ {A E k : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [Ring E] [Algebra A E] [Field k] [Algebra A k] [IsLocalHom (algebraMap A k)] {n : ℕ} (D : W.Det n A E) (π : E →ₐ[A] Matrix (Fin n) (Fin n) k), 1 ≤ n → D.IsCH → Function.Surjective π → (∀ x, (D.chi x).map (algebraMap A k) = (π x).charpoly) →
        ∃ φ : E →ₐ[A] Matrix (Fin n) (Fin n) A, (∀ x, (φ x).map (algebraMap A k) = π x) ∧ ∀ x, D.chi x = (φ x).charpoly := by
  intro A E k _ _ _ _ _ _ _ _ _ n D π hn hD hs hchi
  obtain ⟨hu, hint⟩ := CA.d_unit D hD
  have hunit : ∀ x, π x = 1 → IsUnit x := by
    intro x hx
    rw [hu, ← (CA.d_chi D x).2.2.2.1, W.Det.lam, Nat.sub_self]
    refine (isUnit_one.neg.pow n).mul ?_
    refine (isUnit_map_iff (algebraMap A k) _).1 ?_
    rw [← coeff_map, hchi, hx, coeff_zero_eq_eval_zero, isUnit_iff_ne_zero, Matrix.charpoly_one]
    simp
  have hk : ∀ x, π x = 0 → x ∈ Ring.jacobson E := by
    intro x hx
    rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
    intro y
    obtain ⟨u, hu'⟩ := hunit (y * x + 1) (by simp [hx])
    refine ⟨↑u⁻¹, ?_⟩
    rw [Ideal.mem_bot, sub_eq_zero, ← u.inv_mul, hu', mul_add, mul_one, mul_assoc]
  obtain ⟨e, he, he'⟩ := CA.d_lift_idem π hs hk (fun i => Matrix.single i i (1 : k)) da_coi
  have hrank : ∀ i, D.D A[X] (1 + X ⊗ₜ e i) = 1 + X := by
    intro i
    obtain ⟨r, -, hr⟩ := CA.d_idem_rank D (e i) (he.idem i)
    obtain ⟨s, -, hs'⟩ := CA.d_idem_rank D (1 - e i) (he.idem i).one_sub
    obtain ⟨m, hm⟩ := da_single (k := k) i
    have h1 := hchi (e i)
    rw [da_chi D _ (he.idem i) r s hr hs', he', hm] at h1
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_X, Polynomial.map_one] at h1
    rw [hr, da_one h1, pow_one]
  have hc := fun i => CA.d_corner D (e i) hD (he.idem i) (hrank i) hn
  obtain ⟨φ, hφ, hφ'⟩ := matUnits π e hs he he' (fun i x => ⟨_, (hc i).1 x⟩) (fun i => (hc i).2.2.1)
  refine ⟨φ, hφ', fun x => ?_⟩
  have h := CA.d_gma_det D e hD he hrank A φ hφ A[X] ![X, -1] ![1, x]
  simp only [Fin.sum_univ_two, cons_val_zero, cons_val_one, TensorProduct.neg_tmul, map_one,
    ← sub_eq_add_neg] at h
  rw [W.Det.chi, h, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases hij : i = j
  · subst hij; simp [sub_eq_add_neg]
  · simp [hij]
