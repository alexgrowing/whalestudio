import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDblOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixXChar GlobalTheory.DblEval
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.DiagPos
open MeasureTheory

theorem lDiag_box_conj_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → AF F) → ℂ),
    g ∈ schA F κ → g ≠ 0 → GlobalTheory.DiagForm.lDiag F κ (boxFun g (fun x => starRingEnd ℂ (g x))) ≠ 0 := by
  intro F _ _ κ _ Ψ hΨ h0
  classical
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI := DiagForm.measAf (F := F)
  haveI := DiagForm.borelAf (F := F)
  have hS : boxFun Ψ (fun x => starRingEnd ℂ (Ψ x)) ∈ schA F (κ ⊕ κ) :=
    GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ Ψ hΨ _ (GlobalTheory.SchAConj.star_mem_schA F κ Ψ hΨ)
  have hi := DiagForm.integrable_resD hS
  have hcg : Continuous fun p : DiagForm.Vi F κ × DiagForm.Vf F κ => Ψ (DiagForm.glue p) := by
    have h1 := GlobalTheory.WeilAdm.HaarSplit.continuous_comp_splitE F κ Ψ hΨ
    have h2 : Continuous fun p : DiagForm.Vi F κ × DiagForm.Vf F κ =>
        ((DiagForm.eI F κ p.1, p.2) : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :=
      ((DiagForm.eI F κ).continuous.comp continuous_fst).prodMk continuous_snd
    exact h1.comp h2
  have e : DiagForm.resD F κ (boxFun Ψ fun x => starRingEnd ℂ (Ψ x)) =
      fun p => ((Complex.normSq (Ψ (DiagForm.glue p)) : ℝ) : ℂ) := funext fun p => Complex.mul_conj _
  rw [DiagForm.lDiag, LinearMap.comp_apply, DiagForm.Lext_apply _ hi, e, integral_complex_ofReal,
    Ne, Complex.ofReal_eq_zero]
  intro h1
  rw [e] at hi
  have hi' : Integrable (fun p => Complex.normSq (Ψ (DiagForm.glue p))) (DiagForm.mu F κ) := by
    simpa using hi.re
  have h2 := (integral_eq_zero_iff_of_nonneg (fun p => Complex.normSq_nonneg _) hi').1 h1
  haveI : (DiagForm.mu F κ).IsOpenPosMeasure := by unfold DiagForm.mu; infer_instance
  have h3 := (Continuous.ae_eq_iff_eq _ (Complex.continuous_normSq.comp hcg) continuous_const).1 h2
  refine h0 (funext fun x => ?_)
  have h4 := Complex.normSq_eq_zero.1 (congrFun h3 (0 + DiagForm.shiftOf x))
  simp only [DiagForm.glue_add_shiftOf] at h4
  have h5 : DiagForm.glue (0 : DiagForm.Vi F κ × DiagForm.Vf F κ) = 0 := by
    funext i
    refine Prod.ext ?_ rfl
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (DiagForm.eI F κ 0 i) = 0
    rw [map_zero, Pi.zero_apply, map_zero]
  rwa [h5, zero_add] at h4

end GlobalTheory.DiagPos
