import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem lc_mat {Γ K : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) K)
    (h : ∀ a b, IsLocallyConstant fun g => f g a b) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : ∀ a b, ∀ᶠ y in nhds x, f y a b = f x a b := fun a b =>
    (IsLocallyConstant.iff_eventually_eq _).mp (h a b) x
  filter_upwards [Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr (hx a)] with y hy
  ext a b
  exact hy a b

theorem UpperTheory.V.Th.Coc.lc :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (τ : MonoidAlgebra R G → R) (c c₀ : O) (d : MonoidAlgebra R G →+ Matrix (Fin n) (Fin n) X), (∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) → IsLift x δ (repR x ρ) τ c d → (IsLocallyConstant fun g => bar X (ρ g)) → (IsLocallyConstant fun g => δ (τ (MonoidAlgebra.single g 1))) → IsLocallyConstant fun g => c₀ • d (MonoidAlgebra.single g 1) := by
  intro O R X _ _ _ _ _ n G _ _ _ x δ ρ τ c c₀ d hspan hL hρ hτ
  have hsingle : ∀ g : G, repR x ρ (MonoidAlgebra.single g 1) = ρ g := by
    intro g
    rw [repR_single, map_one, one_smul]
  have hmulD : ∀ g h : G, d (MonoidAlgebra.single (g * h) 1) =
      d (MonoidAlgebra.single g 1) * bar X (ρ h) + bar X (ρ g) * d (MonoidAlgebra.single h 1) := by
    intro g h
    have e := hL.mul (MonoidAlgebra.single g 1) (MonoidAlgebra.single h 1)
    rw [MonoidAlgebra.single_mul_single, mul_one, hsingle, hsingle] at e
    exact e
  have hgen : ∀ h : G, IsLocallyConstant fun g => (d (MonoidAlgebra.single g 1) * bar X (ρ h)).trace := by
    intro h
    have e : (fun g => (d (MonoidAlgebra.single g 1) * bar X (ρ h)).trace) =
        fun g => c • δ (τ (MonoidAlgebra.single (g * h) 1)) -
          (bar X (ρ g) * d (MonoidAlgebra.single h 1)).trace := by
      funext g
      rw [← hL.tr, hmulD, Matrix.trace_add, add_sub_cancel_right]
    rw [e]
    refine IsLocallyConstant.sub ?_ ?_
    · exact (hτ.comp_continuous (continuous_mul_right h)).comp (fun y => c • y)
    · exact hρ.comp fun M => (M * d (MonoidAlgebra.single h 1)).trace
  have hspanLC : ∀ Z ∈ Submodule.span O (Set.range ρ),
      IsLocallyConstant fun g => (d (MonoidAlgebra.single g 1) * bar X Z).trace := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
      obtain ⟨h, rfl⟩ := hZ
      exact hgen h
    | zero =>
      have e : (fun g => (d (MonoidAlgebra.single g 1) * bar X (0 : Matrix (Fin n) (Fin n) O)).trace) =
          fun _ => 0 := by
        funext g
        have hb : bar X (0 : Matrix (Fin n) (Fin n) O) = 0 := by
          ext i j
          simp [bar]
        rw [hb, Matrix.mul_zero, Matrix.trace_zero]
      rw [e]
      exact IsLocallyConstant.const 0
    | add Z W _ _ hZ hW =>
      have e : (fun g => (d (MonoidAlgebra.single g 1) * bar X (Z + W)).trace) =
          fun g => (d (MonoidAlgebra.single g 1) * bar X Z).trace +
            (d (MonoidAlgebra.single g 1) * bar X W).trace := by
        funext g
        have hb : bar X (Z + W) = bar X Z + bar X W := by
          ext i j
          simp [bar]
        rw [hb, Matrix.mul_add, Matrix.trace_add]
      rw [e]
      exact hZ.add hW
    | smul k Z _ hZ =>
      have e : (fun g => (d (MonoidAlgebra.single g 1) * bar X (k • Z)).trace) =
          fun g => algebraMap O X k * (d (MonoidAlgebra.single g 1) * bar X Z).trace := by
        funext g
        have hb : bar X (k • Z) = algebraMap O X k • bar X Z := by
          ext i j
          simp [bar, Matrix.smul_apply, smul_eq_mul]
        rw [hb, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      rw [e]
      exact hZ.comp fun y => algebraMap O X k * y
  apply lc_mat
  intro a b
  have key : ∀ M : Matrix (Fin n) (Fin n) X,
      (M * bar X (c₀ • Matrix.of fun i j => if i = b ∧ j = a then (1:O) else 0)).trace = (c₀ • M) a b := by
    intro M
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, bar, Matrix.map_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_ite, smul_zero, smul_eq_mul, mul_one, ite_and]
    simp only [apply_ite (algebraMap O X), map_zero, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Algebra.smul_def, mul_one]
    rw [mul_comm]
  have e : (fun g => (c₀ • d (MonoidAlgebra.single g 1)) a b) =
      fun g => (d (MonoidAlgebra.single g 1) *
        bar X (c₀ • Matrix.of fun i j => if i = b ∧ j = a then (1:O) else 0)).trace := by
    funext g
    rw [key]
  rw [e]
  exact hspanLC _ (hspan _)
