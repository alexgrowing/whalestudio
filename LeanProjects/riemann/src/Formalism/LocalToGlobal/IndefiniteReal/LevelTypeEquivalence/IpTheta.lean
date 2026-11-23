import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThetaSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff ENNReal

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Basic

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem thetaO_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) := by

  obtain ⟨U1, hU1, h1⟩ := hf.level
  obtain ⟨U2, hU2, h2⟩ := hg.level
  constructor
  · intro γ w
    simp only [Pi.add_apply, hf.quasi, hg.quasi]
    ring
  · refine ⟨U1 ⊓ U2, ?_, fun u hu hfin => ?_⟩
    · first
      | exact hU1.inter hU2
      | simpa using hU1.inter hU2
    · have hu' : u ∈ U1 ∧ u ∈ U2 := by simpa using hu
      funext x
      have e1x := congrFun (h1 u hu'.1 hfin) x
      have e2x := congrFun (h2 u hu'.2 hfin) x
      simp only [heisO, Pi.add_apply] at e1x e2x ⊢
      rw [mul_add, e1x, e2x]
  · exact hf.cont.add hg.cont
  · intro k L hL hfin w
    exact (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w)

theorem thetaO_smul {f : WO S T → ℂ} (c : ℂ) (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by

  obtain ⟨U1, hU1, h1⟩ := hf.level
  constructor
  · intro γ w
    simp only [Pi.smul_apply, smul_eq_mul, hf.quasi]
    ring
  · refine ⟨U1, hU1, fun u hu hfin => ?_⟩
    funext x
    have e1x := congrFun (h1 u hu hfin) x
    simp only [heisO, Pi.smul_apply, smul_eq_mul] at e1x ⊢
    rw [mul_left_comm, e1x]
  · exact hf.cont.const_smul c
  · intro k L hL hfin w
    exact (hf.smooth k L hL hfin w).const_smul c

end Basic

section L2

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

end L2

section Unit

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem norm_weilRepresentation_thetaFunction_preserved (hω : IsWeilDatumO ψ S T χS χT om) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (p : GA D S × GA D T)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : nrm2 μ 𝓕 (om p f) = nrm2 μ 𝓕 f := by
  unfold nrm2
  have hu := hω.om_unit μ 𝓕 hμ h𝓕 p f hf
  simp_rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)] at hu
  have c1 : Continuous fun w => ‖om p f w‖ ^ 2 := (hω.om_pres p f hf).cont.norm.pow 2
  have c2 : Continuous fun w => ‖f w‖ ^ 2 := hf.cont.norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖om p f w‖ ^ 2)
      (Filter.Eventually.of_forall fun _ => by positivity) c1.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖f w‖ ^ 2)
      (Filter.Eventually.of_forall fun _ => by positivity) c2.aestronglyMeasurable, hu]

end Unit

section Cont

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

end Cont

end Formalism.IndefR.Eqv

end
