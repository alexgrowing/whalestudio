import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

noncomputable section

namespace GlobalTheory.CompanionTheory.LFUDom

theorem latchar1 : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ A : GL (Fin 2) F,
  (∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) →
  ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ =
    (((Ad3.LFS.vol2 ψ).real {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} : ℝ) : ℂ) := by
  intro F _ _ _ _ _ _ ψ hψ A hA
  obtain ⟨hc, h1, h0⟩ := hψ
  have ht := isTrivialOn_addCharConductor hc h1
  rw [h0] at ht
  have hopen : IsOpen {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} := by
    have hs : {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} =
        ⋂ i, (fun x : Fin 2 → F => ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i) ⁻¹'
          (valBall F 0 : Set F) := by
      ext x
      simp [mem_valBall_zero_iff]
    rw [hs]
    refine isOpen_iInter_of_finite fun i => (isOpen_valBall _).preimage ?_
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    fun_prop
  have hf : Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]}
        (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) =
      Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]}
        (fun _ => (1 : ℂ)) := by
    refine Set.indicator_congr fun x hx => ?_
    have hx1 : x 1 = (((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
        ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x)) 1 := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hint : x 1 ∈ 𝒪[F] := by
      have key : ∀ y : Fin 2 → F, (∀ i, y i ∈ 𝒪[F]) →
          (((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ y) 1 ∈ 𝒪[F] := fun y hy => by
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        exact add_mem (mul_mem (hA 0) (hy 0)) (mul_mem (hA 1) (hy 1))
      rw [hx1]
      exact key _ hx
    have hb : -x 1 ∈ valBall F 0 := mem_valBall_zero_iff.2 (neg_mem hint)
    rw [ht _ hb]
    simp
  rw [hf, integral_indicator_const _ hopen.measurableSet]
  simp

end GlobalTheory.CompanionTheory.LFUDom
