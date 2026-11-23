import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.FiniteCocyclesColRepOfPhiCond

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private def matrixFlattenLinearEquiv (K : Type) [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n) K ≃ₗ[K] (Fin (n * n) → K) where
  toFun X i := X (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  invFun v a b := v (finProdFinEquiv (a, b))
  map_add' X Y := rfl
  map_smul' c X := rfl
  left_inv X := by
    funext a b
    simp
  right_inv v := by
    funext i
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]

private theorem continuous_matrix_flatten (K : Type) [Field K] [TopologicalSpace K] (n : ℕ) :
    Continuous (matrixFlattenLinearEquiv K n) := by
  show Continuous fun (X : Matrix (Fin n) (Fin n) K) (i : Fin (n * n)) => X (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  exact continuous_pi fun i => (continuous_apply _).comp (continuous_apply _)

private noncomputable def flattenedMatrixRepresentation {K : Type} [Field K] {G : Type} [Group G] {n : ℕ}
    (R : Representation K G (Matrix (Fin n) (Fin n) K)) :
    G →* Matrix (Fin (n * n)) (Fin (n * n)) K where
  toFun g := LinearMap.toMatrix'
    ((matrixFlattenLinearEquiv K n).toLinearMap ∘ₗ R g ∘ₗ (matrixFlattenLinearEquiv K n).symm.toLinearMap)
  map_one' := by
    rw [← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp
  map_mul' g h := by
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp

private theorem matrix_rep_flatten_apply {K : Type} [Field K] {G : Type} [Group G] {n : ℕ}
    (R : Representation K G (Matrix (Fin n) (Fin n) K)) (g : G) (X : Matrix (Fin n) (Fin n) K) :
    Matrix.toLin' (flattenedMatrixRepresentation R g) (matrixFlattenLinearEquiv K n X) = matrixFlattenLinearEquiv K n (R g X) := by
  show Matrix.toLin' (LinearMap.toMatrix' _) _ = _
  rw [Matrix.toLin'_toMatrix']
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply]

private theorem continuous_matrix_rep_flatten {K : Type} [Field K] [TopologicalSpace K] {G : Type} [Group G]
    [TopologicalSpace G] {n : ℕ}
    (R : Representation K G (Matrix (Fin n) (Fin n) K)) (hR : ∀ X, Continuous fun g => R g X) :
    Continuous (flattenedMatrixRepresentation R) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun g => LinearMap.toMatrix' ((matrixFlattenLinearEquiv K n).toLinearMap ∘ₗ R g ∘ₗ (matrixFlattenLinearEquiv K n).symm.toLinearMap) i j
  simp only [LinearMap.toMatrix'_apply]
  exact (continuous_matrix_flatten K n).comp (hR _) |>.comp continuous_id |> fun h => (continuous_apply i).comp h

theorem UpperTheory.V.Th.Det.finite_cocycles_matrixRepresentation_of_phiCond :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {n : ℕ} (R : Representation (Qbar l) G (Matrix (Fin n) (Fin n) (Qbar l))), PhiCond G l → (∀ X, Continuous fun g => R g X) → Module.Finite (Qbar l) (Z1 R) := by
  intro l _ G _ _ _ _ _ n R hΦ hR
  let σ : G →* GL (Fin (n * n)) (Qbar l) := (flattenedMatrixRepresentation R).toHomUnits
  have hσ : Continuous σ := by
    rw [Units.continuous_iff]
    refine ⟨continuous_matrix_rep_flatten R hR, ?_⟩
    have h : (fun g => (((σ g)⁻¹ : GL (Fin (n * n)) (Qbar l)) : Matrix (Fin (n * n)) (Fin (n * n)) (Qbar l))) = fun g => flattenedMatrixRepresentation R g⁻¹ := by
      funext g
      rw [← map_inv]
      rfl
    rw [h]
    exact (continuous_matrix_rep_flatten R hR).comp continuous_inv
  have hfin := UpperTheory.V.Th.Det.finite_cocycles_colRep_of_phiCond σ hΦ hσ
  let Φ : (G → Matrix (Fin n) (Fin n) (Qbar l)) →ₗ[Qbar l] (G → Fin (n * n) → Qbar l) :=
    LinearMap.compLeft (matrixFlattenLinearEquiv (Qbar l) n).toLinearMap G
  have hmem : ∀ f ∈ Z1 R, Φ f ∈ Z1 (UpperTheory.V.Loc.colRep σ) := by
    rintro f ⟨hc, hco⟩
    refine ⟨(continuous_matrix_flatten (Qbar l) n).comp hc, fun g h => ?_⟩
    show matrixFlattenLinearEquiv (Qbar l) n (f (g * h)) = matrixFlattenLinearEquiv (Qbar l) n (f g) + Matrix.toLin' (flattenedMatrixRepresentation R g) (matrixFlattenLinearEquiv (Qbar l) n (f h))
    rw [hco g h, map_add, matrix_rep_flatten_apply]
  have hinj : Function.Injective (Φ.restrict hmem) := by
    intro x y hxy
    apply Subtype.ext
    funext g
    have e := congrFun (congrArg Subtype.val hxy) g
    exact (matrixFlattenLinearEquiv (Qbar l) n).injective e
  exact Module.Finite.of_injective (Φ.restrict hmem) hinj
