import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem isCuspFun_closed : ∀ (D : D7) (V : HSp D) (φ φ' : GA D V → ℂ), IsAutFun V φ → IsAutFun V φ' → IsCuspFun V φ → IsCuspFun V φ' → IsCuspFun V (φ + φ') ∧ (∀ c : ℂ, IsCuspFun V (c • φ)) ∧ (∀ k, IsCuspFun V (rTr V k φ)) ∧ IsCuspFun V (fun g => star (φ g)) := by
  intro D V φ φ' h h' c c'
  refine ⟨?_, fun a r C hC μ 𝓕 hμ h𝓕 g => ?_, fun k r C hC μ 𝓕 hμ h𝓕 g => ?_, fun r C hC μ 𝓕 hμ h𝓕 g => ?_⟩
  · refine (GlobalTheory.AutFunCompare.isCuspFun_iff V (φ + φ') (h.cont.add h'.cont) fun γ hγ g => ?_).2
      (add_mem ((GlobalTheory.AutFunCompare.isCuspFun_iff V φ h.cont h.left).1 c)
        ((GlobalTheory.AutFunCompare.isCuspFun_iff V φ' h'.cont h'.left).1 c'))
    rw [Pi.add_apply, Pi.add_apply, h.left γ hγ, h'.left γ hγ]
  · simp only [Pi.smul_apply]
    rw [integral_smul, c r C hC μ 𝓕 hμ h𝓕 g, smul_zero]
  · simp only [rTr, mul_assoc]
    exact c r C hC μ 𝓕 hμ h𝓕 (g * k)
  · have e := integral_conj (𝕜 := ℂ) (μ := μ.restrict 𝓕) (f := fun n : NI V C => φ ((n : GA D V) * g))
    rw [c r C hC μ 𝓕 hμ h𝓕 g, map_zero] at e
    exact e

end GlobalTheory.Mem.Th
