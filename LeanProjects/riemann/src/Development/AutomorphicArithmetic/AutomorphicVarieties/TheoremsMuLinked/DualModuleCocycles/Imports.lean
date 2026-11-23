import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Kill0

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.kill :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} [IsDomain O] {G : Type} [Group G] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (τ : MonoidAlgebra R G → R) (c c₀ : O) (d : MonoidAlgebra R G →+ Matrix (Fin n) (Fin n) X), c₀ ≠ 0 → (∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) → (∀ y, (repR x ρ y).trace = x (τ y)) → IsLift x δ (repR x ρ) τ c d → ∀ y, (∀ g, τ ((MonoidAlgebra.single g 1) * y) = 0) → repR x ρ y = 0 ∧ c₀ • d y = 0 := by
  intro O R X _ _ _ _ _ n _ G _ x δ ρ τ c c₀ d hc₀ hspan htr hd y hy
  obtain ⟨k1, k2⟩ := kill0 ρ c₀ hc₀ hspan
  have hs : ∀ g : G, repR x ρ (MonoidAlgebra.single g 1) = ρ g := by
    intro g
    rw [repR_single, map_one, one_smul]
  have h1 : repR x ρ y = 0 := by
    apply k1
    intro g
    rw [← hs, ← map_mul, htr, hy, map_zero]
  refine ⟨h1, k2 X (d y) ?_⟩
  intro g
  have e := hd.mul (MonoidAlgebra.single g 1) y
  rw [h1, hs] at e
  have hb0 : bar X (0 : Matrix (Fin n) (Fin n) O) = 0 := by
    ext i j
    simp [bar]
  rw [hb0, Matrix.mul_zero, zero_add] at e
  rw [← e, hd.tr, hy, map_zero, smul_zero]
