import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DAmitsur
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPolyExt

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem d_ext_unit {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D D' : Det n A E)
    {k : ℕ} (x : Fin k → E)
    (h : D.D (MvPolynomial (Fin k) A) (1 + Det.gen x) = D'.D (MvPolynomial (Fin k) A) (1 + Det.gen x))
    (B : Type) [CommRing B] [Algebra A B] (u v : B) (huv : u * v = 1) (b : Fin k → B) :
    D.D B (u ⊗ₜ 1 + ∑ a, b a ⊗ₜ x a) = D'.D B (u ⊗ₜ 1 + ∑ a, b a ⊗ₜ x a) := by
  have e : (u ⊗ₜ[A] (1 : E) + ∑ a, b a ⊗ₜ[A] x a) =
      u • Algebra.TensorProduct.map (MvPolynomial.aeval fun a => v * b a) (AlgHom.id A E) (1 + Det.gen x) := by
    simp only [Det.gen, map_add, map_one, map_sum, Algebra.TensorProduct.map_tmul, MvPolynomial.aeval_X,
      AlgHom.id_apply, smul_add, Finset.smul_sum, smul_tmul', smul_eq_mul, ← mul_assoc, huv, one_mul]
    rw [Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, mul_one]
  rw [e, D.homog, D'.homog, D.nat, D'.nat, h]

private theorem d_ext_poly {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D D' : Det n A E)
    {k : ℕ} (x : Fin k → E)
    (h : D.D (MvPolynomial (Fin k) A) (1 + Det.gen x) = D'.D (MvPolynomial (Fin k) A) (1 + Det.gen x)) :
    D.poly x = D'.poly x := by
  let R := MvPolynomial (Fin k) A
  let L := Localization.Away (X : R[X])
  let y : R[X] ⊗[A] E := (X : R[X]) ⊗ₜ 1 + ∑ a, C (MvPolynomial.X a) ⊗ₜ x a
  have hinj : Function.Injective (algebraMap R[X] L) :=
    IsLocalization.injective L (M := Submonoid.powers (X : R[X]))
      ((Submonoid.powers_le).2 X_mem_nonzeroDivisors)
  have h1 : D.D R[X] y = D'.D R[X] y := by
    apply hinj
    let f : R[X] →ₐ[A] L := IsScalarTower.toAlgHom A R[X] L
    change f _ = f _
    rw [← D.nat, ← D'.nat]
    have e : Algebra.TensorProduct.map f (AlgHom.id A E) y =
        f X ⊗ₜ 1 + ∑ a, f (C (MvPolynomial.X a)) ⊗ₜ x a := by
      simp only [y, map_add, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [e]
    exact d_ext_unit D D' x h L _ (IsLocalization.Away.invSelf (X : R[X]))
      (IsLocalization.Away.mul_invSelf (S := L) (X : R[X])) _
  let g : R[X] →ₐ[A] R := (Polynomial.aeval (0 : R)).restrictScalars A
  have e : Algebra.TensorProduct.map g (AlgHom.id A E) y = Det.gen x := by
    simp only [y, g, map_add, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgHom.coe_restrictScalars', aeval_X, aeval_C, zero_tmul, zero_add, Det.gen]
    rfl
  have h2 := congrArg g h1
  rw [← D.nat, ← D'.nat, e] at h2
  exact h2

theorem UpperTheory.V.CA.d_ext :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (D' : Det n A E) (M : Submonoid E), Submodule.span A (M : Set E) = ⊤ → (∀ x ∈ M, ∀ i, 1 ≤ i → i ≤ n → D.lam i x = D'.lam i x) → D = D' := by
  intro n A E _ _ _ D D' M hM h
  refine d_poly_ext D D' (M : Set E) hM fun k x hx => d_ext_poly D D' x ?_
  ext α
  obtain ⟨P, hP, -, hc⟩ := d_amitsur n k α
  rw [hc D x, hc D' x]
  refine MvPolynomial.eval₂Hom_congr' rfl (fun v hv _ => ?_) rfl
  refine h _ ?_ _ (hP v hv).1 (hP v hv).2.1
  induction v.2 using FreeMonoid.inductionOn' with
  | one => rw [map_one]; exact M.one_mem
  | of_mul a w ih => rw [map_mul, FreeMonoid.lift_eval_of]; exact M.mul_mem (hx a) ih
