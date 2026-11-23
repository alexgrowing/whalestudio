import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem mul_integral_of_integral {F : Type} [Field F] [ValuativeRel F]
    (A : Matrix (Fin 2) (Fin 2) F) (X : Matrix (Fin 2) (Fin 3) F)
    (hA : ∀ i j, A i j ∈ 𝒪[F]) (hX : ∀ i j, X i j ∈ 𝒪[F]) :
    ∀ i j, (A * X) i j ∈ 𝒪[F] := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA i k) (hX k j)

theorem Φ0_integral_mul {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (κ : GL (Fin 2) F) (hκ : κ ∈ integralGL F 2)
    (X : Matrix (Fin 2) (Fin 3) F) :
    Ad3.LFS.Φ0 F ((κ : Matrix (Fin 2) (Fin 2) F) * X) = Ad3.LFS.Φ0 F X := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hκ
  have hiff : (∀ i j, ((κ : Matrix (Fin 2) (Fin 2) F) * X) i j ∈ 𝒪[F]) ↔
      ∀ i j, X i j ∈ 𝒪[F] := by
    refine ⟨fun h => ?_, mul_integral_of_integral _ _ h1⟩
    have hk : ((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((κ : Matrix (Fin 2) (Fin 2) F) * X) = X := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    have := mul_integral_of_integral _ _ h2 h
    rwa [hk] at this
  unfold Ad3.LFS.Φ0
  by_cases hX : ∀ i j, X i j ∈ 𝒪[F]
  · rw [Set.indicator_of_mem (by exact hiff.2 hX), Set.indicator_of_mem (by exact hX)]
    rfl
  · rw [Set.indicator_of_notMem (by exact fun h => hX (hiff.1 h)), Set.indicator_of_notMem (by exact hX)]

theorem inn_Φ0_integral_mul : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (κ : GL (Fin 2) F), κ ∈ integralGL F 2 → ∀ (h : GL (Fin 2) F) (g : GL (Fin 3) F),
    Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) (κ * h) g = Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h g := by
  intro F _ _ _ _ _ _ ψ κ hκ h g
  unfold Ad3.LFS.inn
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, Φ0_integral_mul κ hκ, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.LFUDom
