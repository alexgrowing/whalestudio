import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.occUnit :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) (w : Pl K) (σ : SmIrr (Gw n w)), Occurs μ τ w σ → IsUnitarisable σ.ρ := by
  intro K _ _ n μ _ τ w σ ⟨f, hf0, _, hf⟩
  have hin : ∀ g (x y : LL μ), inner ℂ (rhoL μ w g x) (rhoL μ w g y) = inner ℂ x y := by
    intro g x y
    unfold rhoL
    exact UnitaryRep.inner_map_map _ _ _ _
  have hinj : ∀ v, f v = 0 → v = 0 := by
    have hirr : σ.ρ.IsIrreducible := by cases σ; assumption
    let Q : Subrepresentation σ.ρ := ⟨LinearMap.ker f, fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hf, hv, map_zero]⟩
    rcases eq_bot_or_eq_top Q with h | h
    · intro v hv
      have : v ∈ Q := hv
      rw [h] at this
      exact this
    · exfalso
      apply hf0
      ext1 v
      have : v ∈ Q := by rw [h]; trivial
      exact this
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => inner ℂ (f y) (f x)) ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩
  · intro a b c; simp only [map_add, inner_add_right]
  · intro a b c; simp only [map_smul, inner_smul_right, RingHom.id_apply, smul_eq_mul]
  · intro a b c; simp only [map_add, inner_add_left]
  · intro a b c; simp only [map_smul, inner_smul_left, smul_eq_mul]
  · intro v u; simp only [LinearMap.mk₂'ₛₗ_apply, inner_conj_symm]
  · intro v hv
    simp only [LinearMap.mk₂'ₛₗ_apply]
    exact (re_inner_self_pos (𝕜 := ℂ)).2 (fun h => hv (hinj v h))
  · intro g v u; simp only [LinearMap.mk₂'ₛₗ_apply, hf, hin]
