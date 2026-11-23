import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxLaurDesc :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {X : Type} [AddCommGroup X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] (W : WPres Λ X R) {R' : Type} [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {S : Type} [CommRing S] [Algebra Λ S] [IsCO Λ S] {c : ℕ} {e : S →+* LaurentSeries R'}, Laur Λ c e → ∀ (τ : X →+ ℤ) (F : R →ₐ[Λ] S), (∀ j, ∀ x ∈ W.part j, ∃ y, e (F x) = HahnSeries.single (τ j) y) → ∃ f : W.A →ₐ[Λ] R', ∀ j, ∀ x ∈ W.gr j, e (F x) = HahnSeries.single (τ j) (f x) := by
  intro Λ _ _ X _ _ R _ _ W R' _ _ _ S _ _ _ c e hL τ F hF
  let φ : ∀ j, W.gr j →ₗ[Λ] R' := fun j =>
    { toFun := fun x => (e (F ((x : W.A) : R))).coeff (τ j)
      map_add' := fun x y => by
        simp only [Submodule.coe_add, Subalgebra.coe_add, map_add, HahnSeries.coeff_add]
      map_smul' := fun a x => by
        have h1 : (((a • x : W.gr j) : W.A) : R) = algebraMap Λ R a * ((x : W.A) : R) := by
          rw [← Algebra.smul_def]; rfl
        rw [h1, map_mul, AlgHom.commutes, map_mul, hL.alg, HahnSeries.coeff_single_zero_mul,
          RingHom.id_apply, Algebra.smul_def] }
  have key : ∀ j (x : W.gr j), e (F ((x : W.A) : R)) = HahnSeries.single (τ j) (φ j x) := by
    intro j x
    obtain ⟨y, hy⟩ := hF j ((x : W.A) : R) x.2
    have h2 : φ j x = y := by
      show (e (F ((x : W.A) : R))).coeff (τ j) = y
      rw [hy, HahnSeries.coeff_single_same]
    rw [h2, hy]
  have hone : φ 0 (GradedMonoid.GOne.one (A := fun j => W.gr j)) = 1 := by
    show (e (F 1)).coeff (τ 0) = 1
    rw [map_one, map_one, map_zero, HahnSeries.coeff_one, if_pos rfl]
  have hmul : ∀ {i j} (a : W.gr i) (b : W.gr j), φ _ (GradedMonoid.GMul.mul (A := fun j => W.gr j) a b) = φ i a * φ j b := by
    intro i j a b
    show (e (F (((a : W.A) : R) * ((b : W.A) : R)))).coeff (τ (i + j)) = _
    rw [map_mul, map_mul, key, key, HahnSeries.single_mul_single, map_add, HahnSeries.coeff_single_same]
  refine ⟨(DirectSum.toAlgebra Λ (fun j => W.gr j) φ hone hmul).comp
    (DirectSum.decomposeAlgEquiv W.gr).toAlgHom, fun j x hx => ?_⟩
  have h : DirectSum.decompose W.gr x = DirectSum.of (fun j => W.gr j) j ⟨x, hx⟩ :=
    DirectSum.decompose_of_mem W.gr hx
  have h3 : ((DirectSum.toAlgebra Λ (fun j => W.gr j) φ hone hmul).comp
      (DirectSum.decomposeAlgEquiv W.gr).toAlgHom) x = φ j ⟨x, hx⟩ := by
    show DirectSum.toAlgebra Λ (fun j => W.gr j) φ hone hmul (DirectSum.decompose W.gr x) = _
    rw [h]
    exact DirectSum.toSemiring_of (fun j => (φ j).toAddMonoidHom) hone hmul j _
  rw [h3]
  exact key j ⟨x, hx⟩
