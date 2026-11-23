import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

noncomputable section
open GroundTheory.Global

namespace GlobalTheory.SubstIntertw

variable (F : Type) [Field F] [NumberField F]

def stdChar : AddChar (AF F) ℂ where
  toFun a := (adelicChar F a : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [AddChar.map_add_eq_mul]

theorem stdChar_inl (z : InfiniteAdeleRing F) :
    Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (infiniteAdeleInl z : AF F)) : ℝ)) =
      (adelicChar F (infiniteAdeleInl z) : ℂ) := by
  have h2 : adelicChar F (infiniteAdeleInl z) = Real.fourierChar (-infiniteTrace F z) := adelicChar_infinite z
  rw [h2, GlobalTheory.AdelicSvN.Weyl.trace_eq_mixedTrace, ← mixedTrace_homeomorphMixedSpace, homeomorphMixedSpace_apply,
    Real.fourierChar_apply]
  congr 1
  have : evI F (infiniteAdeleInl z) = InfiniteAdeleRing.ringEquiv_mixedSpace F z := rfl
  rw [this]
  push_cast
  ring

theorem isStd_stdChar : IsStd (stdChar F) := by
  refine ⟨continuous_subtype_val.comp continuous_adelicChar, fun x => ?_, fun a ha => ?_⟩
  · show (adelicChar F (algebraMap F (AF F) x) : ℂ) = 1
    rw [adelicChar_algebraMap]; rfl
  · have h0 : evI F ((0, 1) : AF F) = 0 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
      exact map_zero _
    have h2 : a.2 = 0 := by
      have := congrArg Prod.snd (ha ((0, 1) : AF F) h0)
      have e : (1 : FiniteAdeleRing (𝓞 F) F) * a.2 = 0 := this
      simpa using e
    obtain ⟨z, rfl⟩ : ∃ z : InfiniteAdeleRing F, a = infiniteAdeleInl z := ⟨a.1, Prod.ext rfl h2⟩
    exact (stdChar_inl F z).symm

end GlobalTheory.SubstIntertw

namespace GlobalTheory.SubstIntertw

open GroundTheory.Global

open scoped Classical in

theorem eval_mem_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) x) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • (BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  show pureA F f g x = _
  simp [pureA, mul_comm]

theorem main : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
    ∀ (κ : Type) [Fintype κ], ∀ (T : Module.End ℂ ((κ → AF F) → ℂ)) (a b : (κ → AF F) ≃ₗ[AF F] (κ → AF F)),
    (∀ f ∈ (adeleClass F).adm κ, f ∘ₗ T ∈ (adeleClass F).adm κ) →
    (∀ x y, ∀ Φ ∈ schA F κ, T (schr ψ (x, y) Φ) = schr ψ (a x, b y) (T Φ)) →
    ∃ c : ℂ, ∀ Φ ∈ schA F κ, ∀ x, T Φ x = c * Φ (a.symm x) := by
  intro F _ _ hF ψ hψ κ _ T a b hadm hT
  haveI := hF
  have hstd := isStd_stdChar F
  obtain ⟨α, hα, hαψ⟩ := GlobalTheory.T.exists_ne_zero_adele_char_eq_comp_mul_totally_real F (stdChar F) ψ (GlobalTheory.StdCharFromIsStd.isCharAF hstd) hψ
  set l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0) ∘ₗ T with hl_def
  have hl : l ∈ (adeleClass F).adm κ := hadm _ (eval_mem_adm F κ 0)
  have hinv : ∀ (y : κ → AF F), ∀ φ ∈ schA F κ, l (fun x => stdChar F (x ⬝ᵥ y) * φ x) = l φ := by
    intro y φ hφ
    have e : (fun x => stdChar F (x ⬝ᵥ y) * φ x) = schr ψ (0, algebraMap F (AF F) α⁻¹ • y) φ := by
      funext x
      simp only [schr, zero_dotProduct, mul_zero, add_zero, hαψ, dotProduct_smul, smul_eq_mul, ← mul_assoc,
        ← map_mul, mul_inv_cancel₀ hα, map_one, one_mul]
    rw [e]
    show T (schr ψ (0, _) φ) 0 = T φ 0
    rw [hT _ _ φ hφ]
    simp [schr]
  obtain ⟨c, hc⟩ := GlobalTheory.CharInvForm.main F (stdChar F) hstd κ l hl hinv
  refine ⟨c, fun Φ hΦ x => ?_⟩
  have htr : ∀ v : κ → AF F, schr ψ (v, 0) Φ = schr (stdChar F) (v, 0) Φ := by
    intro v; funext z; simp [schr]
  have hmem : schr ψ (a.symm x, 0) Φ ∈ schA F κ := by
    rw [htr]; exact GlobalTheory.HeisSchA.schr_mem_schA (stdChar F) hstd _ Φ hΦ
  have h1 := hc _ hmem
  have h2 : l (schr ψ (a.symm x, 0) Φ) = T Φ x := by
    show T (schr ψ (a.symm x, 0) Φ) 0 = T Φ x
    rw [hT _ _ Φ hΦ]
    simp [schr]
  rw [← h2, h1]
  congr 1
  simp [schr]

end GlobalTheory.SubstIntertw
