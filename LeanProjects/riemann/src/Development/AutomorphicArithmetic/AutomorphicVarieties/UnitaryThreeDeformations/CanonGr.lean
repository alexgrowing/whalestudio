import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section
open LaurentPolynomial

private theorem exists_coact {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
    (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] :
    ∃ φ : R →+* R[T;T⁻¹], ∀ (j : ℤ) (x : R), x ∈ 𝒜 j ↔ φ x = C x * T j := by
  let t : Multiplicative ℤ →* (R[T;T⁻¹])ˣ := (AddMonoidAlgebra.of R ℤ).toHomUnits
  let φ : R →ₐ[O] R[T;T⁻¹] := act 𝒜 t (IsScalarTower.toAlgHom O R R[T;T⁻¹])
  have h1 : ∀ j x, x ∈ 𝒜 j → φ x = C x * T j := fun j x hx => by
    rw [mul_comm]
    exact act_of_mem 𝒜 t _ hx
  have h2 : ∀ x j, (φ x).coeff j = (DirectSum.decompose 𝒜 x j : R) := by
    intro x j
    induction x using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous i m =>
      rw [h1 i m m.2, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]
      by_cases hij : i = j
      · subst hij
        rw [DirectSum.decompose_of_mem_same 𝒜 m.2, Finsupp.single_eq_same]
      · rw [DirectSum.decompose_of_mem_ne 𝒜 m.2 hij, Finsupp.single_eq_of_ne' hij]
    | add a b ha hb => simp [ha, hb]
  refine ⟨φ, fun j x => ⟨h1 j x, fun hx => ?_⟩⟩
  have h3 := h2 x j
  have hx' : φ x = C x * T j := hx
  rw [hx', ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at h3
  rw [h3]
  exact Subtype.property _

private theorem eig_unique {S n : Type} [CommRing S] [Fintype n] [DecidableEq n]
    (X h g h' : Matrix n n S) (l l' : n → S) (hg : h * g = 1) (gh : g * h = 1)
    (e : X * h = h * diagonal l) (e' : X * h' = h' * diagonal l')
    (o : ∀ a, h a a = 1) (o' : ∀ a, h' a a = 1) (u : ∀ a b, a ≠ b → IsUnit (l a - l' b)) : h' = h := by
  have e1 : g * X = diagonal l * g := by
    calc g * X = g * (X * h) * g := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hg, Matrix.mul_one]
      _ = _ := by rw [e, ← Matrix.mul_assoc, gh, Matrix.one_mul]
  have e2 : diagonal l * (g * h') = (g * h') * diagonal l' := by
    rw [← Matrix.mul_assoc, ← e1, Matrix.mul_assoc, e', Matrix.mul_assoc]
  have e3 : (g * h').IsDiag := by
    intro a b hab
    have := congrFun (congrFun e2 a) b
    rw [diagonal_mul, mul_diagonal] at this
    exact (u a b hab).mul_right_eq_zero.1 (by rw [sub_mul, this]; ring)
  have e4 : h' = h * diagonal (diag (g * h')) := by
    rw [e3.diagonal_diag, ← Matrix.mul_assoc, hg, Matrix.one_mul]
  have e5 : diag (g * h') = fun _ => 1 := by
    funext a
    have := congrFun (congrFun e4 a) a
    rw [mul_diagonal, o, o', one_mul] at this
    exact this.symm
  rw [e4, e5, diagonal_one, Matrix.mul_one]

end

open LaurentPolynomial in
theorem UpperTheory.V.UnitaryThreeInertia.canon_graded :
    ∀ {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Finite R] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (X : Matrix (Fin 3) (Fin 3) R) (h : GL (Fin 3) R), (∀ a b, a ≠ b → IsUnit (X a a - X b b)) → GrMat 𝒜 X → Canon X h → GrMat 𝒜 h.val ∧ GrMat 𝒜 (h⁻¹).val := by
  intro O R _ _ _ _ _ _ 𝒜 _ X h hu hX hc
  obtain ⟨φ, hφ⟩ := exists_coact 𝒜
  have hnil : ∀ x ∈ maximalIdeal R, IsNilpotent x := by
    intro x hx
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rw [hn] at this
    exact this
  set l : Fin 3 → R := diag ((h⁻¹).val * X * h.val) with hl
  have e : X * h.val = h.val * diagonal l := by
    rw [hl, hc.diag.diagonal_diag, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hlX : ∀ a, IsNilpotent (l a - X a a) := by
    intro a
    apply hnil
    have e1 : X * (h.val - 1) = h.val * diagonal l - X := by rw [Matrix.mul_sub, e, Matrix.mul_one]
    have e2 := congrFun (congrFun e1 a) a
    rw [Matrix.sub_apply, mul_diagonal, hc.one, one_mul] at e2
    rw [← e2, Matrix.mul_apply]
    exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _ (hc.hat c a)
  let D : Matrix (Fin 3) (Fin 3) R[T;T⁻¹] := diagonal fun a => T (wt1 a)
  let D' : Matrix (Fin 3) (Fin 3) R[T;T⁻¹] := diagonal fun a => T (-wt1 a)
  have DD : D * D' = 1 := by
    simp only [D, D', diagonal_mul_diagonal, ← T_add, add_neg_cancel, T_zero, diagonal_one]
  have DD' : D' * D = 1 := by
    simp only [D, D', diagonal_mul_diagonal, ← T_add, neg_add_cancel, T_zero, diagonal_one]
  have ent : ∀ (M : Matrix (Fin 3) (Fin 3) R[T;T⁻¹]) a b, (D * M * D') a b = M a b * T (wt a b) := by
    intro M a b
    simp only [D, D', mul_diagonal, diagonal_mul, wt, T_sub]
    ring
  have key : ∀ M : Matrix (Fin 3) (Fin 3) R, GrMat 𝒜 M ↔ M.map φ = D * M.map C * D' := by
    intro M
    constructor
    · intro hM
      ext1 a b
      rw [ent]
      exact (hφ _ _).1 (hM a b)
    · intro hM a b
      have := congrFun (congrFun hM a) b
      rw [ent] at this
      exact (hφ _ _).2 this
  have inv1 : ∀ f : R →+* R[T;T⁻¹], h.val.map f * (h⁻¹).val.map f = 1 := fun f => by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one f (map_zero f) (map_one f)]
  have inv2 : ∀ f : R →+* R[T;T⁻¹], (h⁻¹).val.map f * h.val.map f = 1 := fun f => by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one f (map_zero f) (map_one f)]
  have emap : ∀ f : R →+* R[T;T⁻¹], X.map f * h.val.map f = h.val.map f * diagonal fun a => f (l a) := fun f => by
    rw [← Matrix.map_mul, e, Matrix.map_mul, diagonal_map (map_zero f)]
  have can : ∀ M N : Matrix (Fin 3) (Fin 3) R[T;T⁻¹], (D * M * D') * (D * N * D') = D * (M * N) * D' := by
    intro M N
    calc _ = D * M * (D' * D) * N * D' := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [DD', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have main : D * h.val.map C * D' = h.val.map φ := by
    refine eig_unique (X.map φ) (h.val.map φ) ((h⁻¹).val.map φ) _ (fun a => φ (l a)) (fun a => C (l a))
      (inv1 φ) (inv2 φ) (emap φ) ?_ (fun a => by simp [hc.one]) (fun a => by rw [ent]; simp [hc.one, wt]) ?_
    · rw [(key X).1 hX, can, emap C]
      have hcomm : (diagonal fun a => C (l a)) * D' = D' * diagonal fun a => C (l a) := by
        simp only [D', diagonal_mul_diagonal, mul_comm]
      simp only [Matrix.mul_assoc]
      rw [hcomm]
    · intro a b hab
      have hXa : φ (X a a) = C (X a a) := by
        have := (hφ _ _).1 (hX a a)
        simpa [wt] using this
      have h1 : IsNilpotent (φ (l a - X a a) - C (l b - X b b)) :=
        (Commute.all _ _).isNilpotent_sub ((hlX a).map φ) ((hlX b).map C)
      have h2 := h1.isUnit_add_right_of_commute ((hu a b hab).map C) (Commute.all _ _)
      convert h2 using 1
      simp only [map_sub, hXa]
      ring
  refine ⟨(key _).2 main.symm, (key _).2 ?_⟩
  have h3 : h.val.map φ * (D * (h⁻¹).val.map C * D') = 1 := by
    rw [← main, can, inv1, Matrix.mul_one, DD]
  calc (h⁻¹).val.map φ = (h⁻¹).val.map φ * (h.val.map φ * (D * (h⁻¹).val.map C * D')) := by
        rw [h3, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, inv2, Matrix.one_mul]
