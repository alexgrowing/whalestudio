import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.TwoStepIndep

theorem lintegral_pairOf_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)), StepData σ J x a B J' → IsInvTup R σ J' m' → ∀ (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (g k : HA R σ J), g • ratTup (F := F) R x = k • ratTup (F := F) R x → ∀ f : (Fin 2 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable f → ∫⁻ y', f (pairOf R σ J B y g y') ∂m' = ∫⁻ y', f (pairOf R σ J B y k y') ∂m' := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ _ _ M J x a B J' m' hS hinv y g k hgk f hf
  obtain ⟨-, ⟨e, he, -⟩, -⟩ := GlobalTheory.FrameStep.frameStep F E σ hCM R M J x a B J' hS
  have hmem : k⁻¹ * g ∈ Hstab R σ J x := by
    have : (k⁻¹ * g) • ratTup (F := F) R x = ratTup (F := F) R x := by
      rw [mul_smul, hgk, inv_smul_smul]
    exact this
  have hrel : FrameRelR R σ J J' B (k⁻¹ * g) (e ⟨k⁻¹ * g, hmem⟩) := he ⟨k⁻¹ * g, hmem⟩
  set u := e ⟨k⁻¹ * g, hmem⟩ with hu
  have hkey : ∀ y', pairOf R σ J B y g y' = pairOf R σ J B y k (u • y') := by
    intro y'
    have hg : g = k * (k⁻¹ * g) := by group
    have h1 : ((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) =
        ((HA.mat R σ J k : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) *
        ((HA.mat R σ J (k⁻¹ * g) : GL (Fin (M + 1)) (R ⊗[F] E)) :
          Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) := by
      conv_lhs => rw [hg]
      rfl
    have h2 : (u • y') 0 = ((HA.mat R σ J' u : GL (Fin M) (R ⊗[F] E)) :
        Matrix _ _ (R ⊗[F] E)).mulVec (y' 0) := rfl
    unfold FrameRelR at hrel
    unfold pairOf
    rw [h1, h2]
    simp only [Matrix.mulVec_mulVec]
    rw [Matrix.mul_assoc]
    exact congrArg (fun A : Matrix (Fin (M + 1)) (Fin M) (R ⊗[F] E) =>
      (![y 0, (((HA.mat R σ J k : GL (Fin (M + 1)) (R ⊗[F] E)) :
        Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) * A).mulVec (y' 0)] :
          Fin 2 → Fin (M + 1) → R ⊗[F] E)) hrel
  have hc : Continuous fun y' => pairOf R σ J B y k y' := by
    refine continuous_pi ?_
    rw [Fin.forall_fin_two]
    refine ⟨continuous_const, ?_⟩
    have h0 : Continuous fun y' : Fin 1 → Fin M → R ⊗[F] E => y' 0 := continuous_apply 0
    show Continuous fun y' : Fin 1 → Fin M → R ⊗[F] E =>
      ((HA.mat R σ J k : GL (Fin (M + 1)) (R ⊗[F] E)) :
        Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)).mulVec ((B.map (inclR R)).mulVec (y' 0))
    exact continuous_const.matrix_mulVec (continuous_const.matrix_mulVec h0)
  have hm : Measurable fun X : Fin 1 → Fin M → R ⊗[F] E => u • X :=
    (continuous_const_smul u).measurable
  simp_rw [hkey]
  conv_rhs => rw [← hinv u]
  exact (lintegral_map (hf.comp hc.measurable) hm).symm

end GlobalTheory.TwoStepIndep
