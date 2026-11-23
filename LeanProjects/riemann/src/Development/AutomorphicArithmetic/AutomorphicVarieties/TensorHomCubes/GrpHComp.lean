import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

open CategoryTheory Simplicial UpperTheory.V.KL

theorem UpperTheory.V.KL.grpHComp :
    (∀ (G : Type) [Group G] (n : ℕ), grpHMap (MonoidHom.id G) n = 𝟙 _) ∧
      ∀ (G H K : Type) [Group G] [Group H] [Group K] (f : G →* H) (g : H →* K) (n : ℕ),
        grpHMap (g.comp f) n = grpHMap f n ≫ grpHMap g n := by
  refine ⟨fun G _ n => groupHomology.map_id n, fun G H K _ _ _ f g n => ?_⟩
  unfold grpHMap
  rw [← groupHomology.map_comp]
  rfl
