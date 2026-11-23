import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.ideleCongruenceCondition_mul_congruenceUnit_iff :
    ∀ N : ℕ, 0 < N → ∀ τ ∈ TT N, ∀ y : (A ℚ)ˣ, ((∀ v, Bad N v → Dv N v (((y * τ : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y * τ : (A ℚ)ˣ) : A ℚ)) ≤ 1) ↔ ((∀ v, Bad N v → Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) ≤ 1) := by
  intro N _ τ hτ y
  obtain ⟨⟨_, hu⟩, hd⟩ := hτ
  have h1 : ∀ v : H.P ℚ, Valued.v (H.cp v ((y * τ : (A ℚ)ˣ) : A ℚ)) = Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) := by
    intro v
    rw [Units.val_mul, map_mul, map_mul, hu v, mul_one]
  have h2 : ∀ v : H.P ℚ, Dv N v (((y * τ : (A ℚ)ˣ) : A ℚ) - 1) ↔ Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1) := by
    intro v
    have hv := hd v
    have he : Valued.v (H.cp v (((y : A ℚ) - 1) * (τ : A ℚ))) = Valued.v (H.cp v ((y : A ℚ) - 1)) := by
      rw [map_mul, map_mul, hu v, mul_one]
    unfold Dv at hv ⊢
    constructor
    · intro h
      have e : ((y : A ℚ) - 1) * (τ : A ℚ) = (((y * τ : (A ℚ)ˣ) : A ℚ) - 1) - ((τ : A ℚ) - 1) := by
        rw [Units.val_mul]; ring
      rw [← he, e, map_sub]
      exact Valuation.map_sub_le _ h hv
    · intro h
      have e : (((y * τ : (A ℚ)ˣ) : A ℚ) - 1) = ((y : A ℚ) - 1) * (τ : A ℚ) + ((τ : A ℚ) - 1) := by
        rw [Units.val_mul]; ring
      rw [e, map_add]
      exact Valuation.map_add_le _ (he ▸ h) hv
  simp only [h1, h2]
