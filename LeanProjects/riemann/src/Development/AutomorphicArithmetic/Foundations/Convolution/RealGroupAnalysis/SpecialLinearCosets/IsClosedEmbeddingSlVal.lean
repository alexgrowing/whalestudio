import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.ClosedEmbeddingVal
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IndicatorMemSB
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.DetMulInv

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem isClosedEmbedding_slVal {F : Type} [Field F] [NumberField F] (v : P F) :
    IsClosedEmbedding (fun m : SL v => (m.1 : M2 v)) := by
  have hc : IsClosed {A : M2 v | A.det = 1} :=
    isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
  exact hc.isClosedEmbedding_subtypeVal

private noncomputable def resL {F : Type} [Field F] [NumberField F] (v : P F) :
    SB (M2 v) →ₗ[ℂ] SB (SL v) where
  toFun b := ⟨fun m => b.1 m.1,
    b.2.1.comp_continuous (isClosedEmbedding_slVal v).continuous,
    b.2.2.comp_isClosedEmbedding (isClosedEmbedding_slVal v)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def trM {F : Type} [Field F] [NumberField F] {v : P F} (g : SL v)
    (b : SB (M2 v)) : SB (M2 v) :=
  let e : M2 v ≃ₜ M2 v :=
    { toFun := fun m => m * g.1
      invFun := fun m => m * (g⁻¹ : SL v).1
      left_inv := fun m => by
        show m * g.1 * (g⁻¹ : SL v).1 = m
        rw [mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, mul_one]
      right_inv := fun m => by
        show m * (g⁻¹ : SL v).1 * g.1 = m
        rw [mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, mul_one]
      continuous_toFun := continuous_id.matrix_mul continuous_const
      continuous_invFun := continuous_id.matrix_mul continuous_const }
  ⟨fun m => b.1 (e m), b.2.1.comp_continuous e.continuous, b.2.2.comp_homeomorph e⟩

theorem UpperTheory.ConvolutionTheory.R2.I.absM :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLv v) V), (∀ f, IsOpen {g | ρ g f = f}) →
      ∀ β : V →ₗ[ℂ] SB (M2 v) →ₗ[ℂ] ℂ,
      (∀ (g : SL v) f (a a' : SB (M2 v)), (∀ m, a'.1 m = a.1 (m * g.1)) → β (ρ (Matrix.SpecialLinearGroup.toGL g) f) a' = β f a) →
      (∀ f (s : Kv v) (a a' : SB (M2 v)), (∀ m, a'.1 m = ψl v (-(s * m.det)) * a.1 m) → β f a' = ψl v (-s) * β f a) →
      ∀ f (a : SB (M2 v)) (aa : GLv v → SB (M2 v)),
        (∀ x m, (aa x).1 m = a.1 ((x⁻¹).val * m * (dd x).val)) → (fun x => β (ρ (dd x) f) (aa x)) ∈ MC ρ := by
  intro F _ _ v V _ _ ρ hρ β hinv hψ f a aa haa
  have hsurj : Function.Surjective (resL v) := by
    intro c
    obtain ⟨b, hb⟩ := UpperTheory.ConvolutionTheory.R2.I.ext F v c
    exact ⟨b, Subtype.ext (funext hb)⟩
  obtain ⟨s, hs⟩ := (resL v).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  have hs' : ∀ c, resL v (s c) = c := fun c => LinearMap.congr_fun hs c
  have hdep : ∀ (h : V) (b : SB (M2 v)), β h (s (resL v b)) = β h b := by
    intro h b
    have hz : β h (s (resL v b) - b) = 0 := by
      refine UpperTheory.ConvolutionTheory.R2.I.loc F v (β h) (fun t a a' ha => hψ h t a a' ha) _ ?_
      intro m hm
      have h1 : (s (resL v b)).1 m = b.1 m :=
        congrArg (fun c : SB (SL v) => c.1 ⟨m, hm⟩) (hs' (resL v b))
      show (s (resL v b)).1 m - b.1 m = 0
      rw [h1, sub_self]
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  have key := UpperTheory.ConvolutionTheory.R2.I.absS F v V ρ hρ (β.compl₂ s) ?_ f (resL v a)
    (fun x => resL v (aa x)) ?_
  · have hfun : (fun x => β (ρ (dd x) f) (aa x)) =
        fun x => (β.compl₂ s) (ρ (dd x) f) (resL v (aa x)) := by
      funext x
      rw [LinearMap.compl₂_apply, hdep]
    rw [hfun]
    exact key
  · intro g h c c' hc
    rw [LinearMap.compl₂_apply, LinearMap.compl₂_apply]
    have e : resL v (trM g (s c)) = c' := by
      apply Subtype.ext
      funext m
      have h1 : (s c).1 (m * g).1 = c.1 (m * g) :=
        congrArg (fun d : SB (SL v) => d.1 (m * g)) (hs' c)
      rw [hc m, ← h1]
      rfl
    rw [← e, hdep]
    exact hinv g h (s c) (trM g (s c)) (fun m => rfl)
  · intro x m m' hm
    show (aa x).1 m.1 = a.1 m'.1
    rw [haa, hm]
