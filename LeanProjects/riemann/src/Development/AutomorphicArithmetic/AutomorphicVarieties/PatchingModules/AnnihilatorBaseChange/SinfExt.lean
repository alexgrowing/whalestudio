import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.sinfExt :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (D q n : ℕ) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (a : Unit ⊕ Fin D → R) (y : Fin q × Fin n → R), (∀ k, a k ∈ maximalIdeal R) → (∀ p, y p ∈ maximalIdeal R) → ∃! s : Sinf O Unit D q n →ₐ[O] R, (∀ k, s (MvPowerSeries.C (MvPowerSeries.X k)) = a k) ∧ ∀ p, s (MvPowerSeries.X p) = y p := by
  intro O _ _ _ _ D q n R _ _ _ a y ha hy
  haveI hO : IsCO O O :=
    { complete := inferInstance
      isLocalHom := ⟨fun x hx => by simpa using hx⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hL : IsCO O (abelian₂ O Unit D) := co_mvps O O (Unit ⊕ Fin D)
  obtain ⟨F1, ⟨hF1C, hF1X⟩, hF1u⟩ := co_ev O O R (Unit ⊕ Fin D) (Algebra.ofId O R) a ha
  obtain ⟨F2, ⟨hF2C, hF2X⟩, hF2u⟩ := co_ev O (abelian₂ O Unit D) R (Fin q × Fin n) F1 y hy
  refine ⟨F2, ⟨fun k => by rw [hF2C, hF1X], hF2X⟩, ?_⟩
  rintro s ⟨hsC, hsX⟩
  let G : abelian₂ O Unit D →ₐ[O] R :=
    s.comp (IsScalarTower.toAlgHom O (abelian₂ O Unit D) (Sinf O Unit D q n))
  have hGapp : ∀ x, G x = s (MvPowerSeries.C x) := by
    intro x
    simp [G, MvPowerSeries.algebraMap_apply]
  have hG : G = F1 := by
    apply hF1u G
    refine ⟨fun x => ?_, fun k => ?_⟩
    · have h1 : (MvPowerSeries.C x : abelian₂ O Unit D) = algebraMap O (abelian₂ O Unit D) x := by
        simp [MvPowerSeries.algebraMap_apply]
      rw [h1, G.commutes]
      rfl
    · rw [hGapp, hsC k]
  apply hF2u s
  refine ⟨fun x => ?_, hsX⟩
  rw [← hG, hGapp]
