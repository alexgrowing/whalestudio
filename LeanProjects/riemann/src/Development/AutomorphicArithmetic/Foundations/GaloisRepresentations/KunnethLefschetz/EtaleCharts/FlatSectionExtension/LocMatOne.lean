import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatOne :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) {V : Scheme.{0}} (p : V ⟶ W), (∀ x : V, (p ≫ i) x ∈ B.V α) → LocMat B α α p 1 := by
  intro K _ W Z Y q i π D d B α V p h x
  have hU : ⊤ ≤ (((⊤ : V.Opens).ι ≫ p ≫ i) ⁻¹ᵁ B.V α) := by
    intro y _
    exact h y.1
  refine ⟨⊤, B.V α, trivial, (B.c α).affine, le_rfl, le_rfl, hU, 1, ?_, ?_⟩
  · intro m
    simp [Matrix.one_apply]
  · rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
