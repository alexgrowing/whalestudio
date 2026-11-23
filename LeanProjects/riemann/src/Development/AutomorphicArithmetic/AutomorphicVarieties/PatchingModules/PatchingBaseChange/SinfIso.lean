import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilMvps

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem UpperTheory.V.Pa.BC.mvps_congr (K A B σ : Type) [CommRing K] [CommRing A] [CommRing B] [Algebra K A]
    [Algebra K B] (e : A ≃ₐ[K] B) :
    ∃ E : MvPowerSeries σ A ≃ₐ[K] MvPowerSeries σ B, ∀ a, E a = MvPowerSeries.map (e : A →+* B) a := by
  have h1 : ∀ φ : MvPowerSeries σ A,
      MvPowerSeries.map (e.symm : B →+* A) (MvPowerSeries.map (e : A →+* B) φ) = φ := by
    intro φ
    ext n
    simp
  have h2 : ∀ φ : MvPowerSeries σ B,
      MvPowerSeries.map (e : A →+* B) (MvPowerSeries.map (e.symm : B →+* A) φ) = φ := by
    intro φ
    ext n
    simp
  let f : MvPowerSeries σ A ≃+* MvPowerSeries σ B :=
    { toFun := MvPowerSeries.map (e : A →+* B)
      invFun := MvPowerSeries.map (e.symm : B →+* A)
      left_inv := h1
      right_inv := h2
      map_mul' := map_mul _
      map_add' := map_add _ }
  refine ⟨AlgEquiv.ofRingEquiv (f := f) ?_, fun a => ?_⟩
  · intro k
    simp [f, MvPowerSeries.algebraMap_apply]
  · rfl

theorem UpperTheory.V.Pa.BC.sinf_iso :
    ∀ (l : ℕ) (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] (D q n : ℕ) (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D), (∀ a, τ (Til.ι O O' _ a) = lamEmb O O' D a) → ∃ τS : Til O O' (Sinf O Empty D q n) ≃ₐ[O'] Sinf O' Unit D q n, SinfRel l τ τS := by
  intro l O O' _ _ _ _ _ D q n τ hτ
  obtain ⟨τ0, h0ι, -, -, h0c⟩ :=
    UpperTheory.V.Pa.BC.til_mvps O O' (abelian₂ O Empty D) (Fin q × Fin n)
  obtain ⟨E, hE⟩ :=
    UpperTheory.V.Pa.BC.mvps_congr O' (Til O O' (abelian₂ O Empty D)) (abelian₂ O' Unit D) (Fin q × Fin n) τ
  have key : ∀ x : MvPowerSeries (Fin q × Fin n) (abelian₂ O Empty D),
      (τ0.trans E) (Til.ι O O' _ x) = MvPowerSeries.map ((τ : _ →+* _).comp (Til.ι O O' _)) x := by
    intro x
    rw [AlgEquiv.trans_apply, h0ι, hE, ← RingHom.comp_apply, ← MvPowerSeries.map_comp]
  refine ⟨τ0.trans E, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro p
    rw [key, MvPowerSeries.map_X]
  · intro a
    rw [key, MvPowerSeries.map_C, RingHom.comp_apply]
    simp [hτ]
  · intro c hc z
    rw [AlgEquiv.trans_apply, hE, MvPowerSeries.constantCoeff_map, h0c c hc z]
    rfl
  · intro a
    unfold delIdeal
    rw [Ideal.map_span, ← Set.range_comp]
    congr 1
    congr 1
    funext p
    simp only [Function.comp_apply, RingHom.comp_apply]
    erw [key]
    simp [MvPowerSeries.map_X]
