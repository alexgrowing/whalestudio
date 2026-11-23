import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

namespace GlobalTheory.DiagSq

open GlobalTheory.DiagForm
open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

local instance measAf' : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
local instance borelAf' : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩

instance mu_openPos : (mu F κ).IsOpenPosMeasure := by unfold mu; infer_instance

theorem pureA_glue (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (p : Vi F κ × Vf F κ) : pureA F f g (glue p) = f (eI F κ p.1) * g p.2 := by
  change f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (glue p i).1) * g (fun i => (glue p i).2) = _
  congr 2 <;> funext i <;> simp [glue]

theorem continuous_glue {φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hφ : φ ∈ schA F κ) :
    Continuous fun p : Vi F κ × Vf F κ => φ (glue p) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    simp only [pureA_glue]
    exact (f.continuous.comp ((eI F κ).continuous.comp continuous_fst)).mul (hg.1.continuous.comp continuous_snd)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact continuous_const.mul hx

theorem glue_shiftOf (x : κ → AF F) : glue (shiftOf x) = x := by
  have h := glue_add_shiftOf (0 : Vi F κ × Vf F κ) x
  rw [zero_add] at h
  rw [h]
  have h0 : glue (0 : Vi F κ × Vf F κ) = 0 := by
    funext i
    refine Prod.ext ?_ ?_
    · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ 0 i) = 0
      simp
    · rfl
  rw [h0, zero_add]

theorem lDiag_boxFun_star_ne : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : (κ → AF F) → ℂ),
    φ ∈ schA F κ → φ ≠ 0 → GlobalTheory.DiagForm.lDiag F κ (boxFun φ (star φ)) ≠ 0 := by
  intro F _ _ κ _ φ hφ hne
  have hs : star φ ∈ schA F κ := GlobalTheory.SchAConj.star_mem_schA F κ φ hφ
  have hb := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ φ hφ (star φ) hs
  have hi := integrable_resD hb
  have e : resD F κ (boxFun φ (star φ)) = fun p => ((Complex.normSq (φ (glue p)) : ℝ) : ℂ) := by
    funext p
    show φ (Sum.elim (glue p) (glue p) ∘ Sum.inl) * star φ (Sum.elim (glue p) (glue p) ∘ Sum.inr) = _
    rw [Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.star_apply, Complex.star_def, Complex.mul_conj]
  rw [lDiag, LinearMap.comp_apply, Lext_apply _ hi, e, integral_complex_ofReal, Complex.ofReal_ne_zero]
  rw [e] at hi
  have hr : Integrable (fun p => Complex.normSq (φ (glue p))) (mu F κ) := by
    simpa using hi.re
  have hc : Continuous fun p => Complex.normSq (φ (glue p)) :=
    Complex.continuous_normSq.comp (continuous_glue hφ)
  obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  refine ((integral_pos_iff_support_of_nonneg (fun p => Complex.normSq_nonneg _) hr).2 ?_).ne'
  refine hc.isOpen_support.measure_pos _ ⟨shiftOf x, ?_⟩
  rw [Function.mem_support, glue_shiftOf]
  exact (Complex.normSq_pos.2 hx).ne'

end GlobalTheory.DiagSq
