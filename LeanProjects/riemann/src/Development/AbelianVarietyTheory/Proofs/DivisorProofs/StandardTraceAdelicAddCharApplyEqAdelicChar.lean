import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

namespace GlobalTheory.StdCharEq

theorem trace_eq_infiniteTrace (F : Type) [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) =
      GroundTheory.Global.infiniteTrace F x := by
  classical
  rw [← GroundTheory.Global.mixedTrace_homeomorphMixedSpace, GroundTheory.Global.homeomorphMixedSpace_apply,
    GroundTheory.Global.mixedTrace_apply, Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi,
    PI.ProdFormulaE.Tr.trace_pi]
  simp only [Algebra.trace_self_apply, Algebra.trace_complex_apply]

theorem eq_adelicChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ x : AF F, ψ x = (GroundTheory.Global.adelicChar F x : ℂ) := by
  intro F _ _ ψ hψ
  have hadd : ∀ a b : AF F, (GroundTheory.Global.adelicChar F (a + b) : ℂ) =
      (GroundTheory.Global.adelicChar F a : ℂ) * (GroundTheory.Global.adelicChar F b : ℂ) := fun a b => by
    rw [← Circle.coe_mul]
    exact congrArg _ ((GroundTheory.Global.adelicChar F).map_add_eq_mul a b)
  have hinf : ∀ x : Ainf F, ψ (pairA F x 0) = (GroundTheory.Global.adelicChar F (pairA F x 0) : ℂ) := fun x => by
    have h : GroundTheory.Global.adelicChar F (pairA F x 0) = 𝐞 (-GroundTheory.Global.infiniteTrace F x) :=
      GroundTheory.Global.adelicChar_infinite x
    rw [GlobalTheory.StdCharFromIsStd.psi_pairA hψ, trace_eq_infiniteTrace, h, Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  have hp : Continuous fun y : Af F => pairA F 0 y := continuous_const.prodMk continuous_id
  have hc : Continuous fun a : AF F => (GroundTheory.Global.adelicChar F a : ℂ) :=
    continuous_subtype_val.comp GroundTheory.Global.continuous_adelicChar
  have hcl : IsClosed {y : Af F | ψ (pairA F 0 y) = (GroundTheory.Global.adelicChar F (pairA F 0 y) : ℂ)} :=
    isClosed_eq (hψ.1.comp hp) (hc.comp hp)
  have hrange : Set.range (algebraMap F (Af F)) ⊆
      {y : Af F | ψ (pairA F 0 y) = (GroundTheory.Global.adelicChar F (pairA F 0 y) : ℂ)} := by
    rintro _ ⟨a, rfl⟩
    have h1 := hψ.2.1 a
    have h2 : (GroundTheory.Global.adelicChar F (algebraMap F (AF F) a) : ℂ) = 1 := by
      have h := GroundTheory.Global.adelicChar_algebraMap (K := F) a
      exact (congrArg (fun z : Circle => (z : ℂ)) h).trans Circle.coe_one
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, AddChar.map_add_eq_mul, hinf] at h1
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, hadd] at h2
    exact mul_left_cancel₀ (Circle.coe_ne_zero _) (h1.trans h2.symm)
  have hall := hcl.closure_subset_iff.2 hrange
  rw [GlobalTheory.AdeleCharTwist.denseRange_fin.closure_range] at hall
  intro x
  rw [GlobalTheory.StdCharFromIsStd.pairA_split x, AddChar.map_add_eq_mul, hadd, hinf]
  exact congrArg _ (hall (Set.mem_univ x.2))

end GlobalTheory.StdCharEq
