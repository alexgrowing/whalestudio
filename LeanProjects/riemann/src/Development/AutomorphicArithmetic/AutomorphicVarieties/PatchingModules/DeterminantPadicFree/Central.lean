import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.central :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (Z : Matrix (Fin n) (Fin n) F), (∀ g ∈ D.G', D.r g * Z = Z * D.r g) → (Z ∈ Od F F n D.a → Z = 0) ∧ (Z ∈ Ev F F n D.a → ∀ g, D.r g * Z = Z * D.r g) := by
  intro F G _ _ n D Z hZ
  have key : ∀ X ∈ Ev F F n D.a, X * Z = Z * X := by
    intro X hX
    rw [← D.span] at hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      exact hZ g hg
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
    | smul c x _ hx => rw [Matrix.smul_mul, Matrix.mul_smul, hx]
  refine ⟨fun hO => ?_, fun _ g => key _ (D.ev g)⟩
  ext i j
  by_cases hij : ((i : ℕ) < D.a ↔ (j : ℕ) < D.a)
  · simpa using (hO i j).1 hij
  · have hne : i ≠ j := fun h => hij (by rw [h])
    have hE : Matrix.diagonal (Pi.single i (1 : F)) ∈ Ev F F n D.a := by
      intro p q
      refine ⟨fun _ => Submodule.mem_top, fun h => ?_⟩
      have hpq : p ≠ q := fun e => h (by rw [e])
      simp [Matrix.diagonal_apply_ne _ hpq]
    have h := congrFun (congrFun (key _ hE) i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
    simpa [Pi.single_eq_of_ne hne.symm] using h
