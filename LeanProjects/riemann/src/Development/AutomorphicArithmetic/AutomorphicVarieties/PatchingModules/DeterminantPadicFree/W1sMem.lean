import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.w1sMem :
    ∀ {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}, (∀ Z : Matrix (Fin n) (Fin n) (DD X g), Z ∈ pairedDualFirstOrderDualMatrixSpace n A X g a → etaM Z ∈ Ev A X n a ∧ ∀ j, ep'M j Z ∈ Od A X n a) ∧ (∀ Z ∈ pairedDualFirstOrderDualMatrixSpace n A X g a, ∀ Z' ∈ pairedDualFirstOrderDualMatrixSpace n A X g a, etaM Z = etaM Z' → (∀ j, ep'M j Z = ep'M j Z') → Z = Z') ∧ ∀ (Y₀ : Matrix (Fin n) (Fin n) X) (Y : Fin g → Matrix (Fin n) (Fin n) X), Y₀ ∈ Ev A X n a → (∀ j, Y j ∈ Od A X n a) → ∃ Z ∈ pairedDualFirstOrderDualMatrixSpace n A X g a, etaM Z = Y₀ ∧ ∀ j, ep'M j Z = Y j := by
  intro A X _ _ _ g n a
  have hW : ∀ Z : Matrix (Fin n) (Fin n) (DD X g), Z ∈ pairedDualFirstOrderDualMatrixSpace n A X g a ↔ ∀ i j : Fin n,
      ((↑i < a ↔ ↑j < a) → (Z i j).a = 0 ∧ (Z i j).ep = 0 ∧ (Z i j).ep' = 0) ∧
      (¬(↑i < a ↔ ↑j < a) → (Z i j).a = 0 ∧ (Z i j).ep = 0 ∧ (Z i j).eta = 0) := by
    intro Z
    simp [pairedDualFirstOrderDualMatrixSpace, blkMat, ddPart]
  have hE : ∀ Y : Matrix (Fin n) (Fin n) X, Y ∈ Ev A X n a ↔
      ∀ i j : Fin n, ¬(↑i < a ↔ ↑j < a) → Y i j = 0 := by
    intro Y
    simp [Ev, blkMat]
  have hO : ∀ Y : Matrix (Fin n) (Fin n) X, Y ∈ Od A X n a ↔
      ∀ i j : Fin n, (↑i < a ↔ ↑j < a) → Y i j = 0 := by
    intro Y
    simp [Od, blkMat]
  refine ⟨?_, ?_, ?_⟩
  · intro Z hZ
    rw [hW] at hZ
    refine ⟨(hE _).2 fun i j hij => ((hZ i j).2 hij).2.2, fun l => (hO _).2 fun i j hij => ?_⟩
    simp only [ep'M, Matrix.map_apply]
    rw [((hZ i j).1 hij).2.2]
    rfl
  · intro Z hZ Z' hZ' he hp
    rw [hW] at hZ hZ'
    funext i j
    have h1 := congrFun (congrFun he i) j
    have h2 : ∀ l, (Z i j).ep' l = (Z' i j).ep' l := fun l => congrFun (congrFun (hp l) i) j
    simp only [etaM, Matrix.map_apply] at h1
    have ha : (Z i j).a = (Z' i j).a ∧ (Z i j).ep = (Z' i j).ep := by
      by_cases hij : (↑i < a ↔ ↑j < a)
      · rw [((hZ i j).1 hij).1, ((hZ' i j).1 hij).1, ((hZ i j).1 hij).2.1, ((hZ' i j).1 hij).2.1]
        exact ⟨rfl, rfl⟩
      · rw [((hZ i j).2 hij).1, ((hZ' i j).2 hij).1, ((hZ i j).2 hij).2.1, ((hZ' i j).2 hij).2.1]
        exact ⟨rfl, rfl⟩
    exact DD.ext ha.1 ha.2 (funext h2) h1
  · intro Y₀ Y h0 hY
    rw [hE] at h0
    refine ⟨Matrix.of fun i j => ⟨0, 0, fun l => Y l i j, Y₀ i j⟩, (hW _).2 fun i j =>
      ⟨fun hij => ⟨rfl, rfl, funext fun l => (hO _).1 (hY l) i j hij⟩, fun hij => ⟨rfl, rfl, h0 i j hij⟩⟩,
      rfl, fun l => rfl⟩
