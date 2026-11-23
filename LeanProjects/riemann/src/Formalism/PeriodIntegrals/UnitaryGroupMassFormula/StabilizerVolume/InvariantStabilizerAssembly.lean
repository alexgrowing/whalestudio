import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.NuNeSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnimodStab
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExFDStabFin

noncomputable section

namespace PI.VolStabS.InvariantStabilizerAssembly

open PI.VolStabS MeasureTheory Measure Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.VolFromSW
open scoped TensorProduct

theorem invStab_of_lamEx (hLam : LamEx) : InvStab := by
  intro F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ'' hμ''
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  obtain ⟨μ, hμ⟩ := hSWa1.1
  have : μ.IsHaarMeasure := hμ
  have : SigmaCompactSpace (HA (AF F) σ J) := um_sigmaCompact_HA F E σ M J hSWa1
  have : IsMulRightInvariant μ :=
    unimod_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ hμ
  have hcl := us_isClosed_stab F E σ M a J X0
  have : LocallyCompactSpace (stabT (AF F) σ J X0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SigmaCompactSpace (stabT (AF F) σ J X0) := hcl.sigmaCompactSpace
  obtain ⟨lam, μ0, hμ0, hC, -⟩ :=
    hLam F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ hμ
  let s : (Fin a → Fin M → AF F ⊗[F] E) → HA (AF F) σ J := fun y =>
    if h : ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) X0 = y then h.choose else 1
  have hs : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) X0 = y) →
      s y • ratTup (F := F) (AF F) X0 = y := by
    intro y h
    simp only [s, dif_pos h]
    exact h.choose_spec
  have : IsMulRightInvariant μ0 :=
    us_rightInv_of_compat μ (stabT (AF F) σ J X0).subtype μ0 lam s (fun f hf => hC.2 f hf s hs)
  have hc : μ'' = haarScalarFactor μ'' μ0 • μ0 := um_eq_smul_of_sigmaCompact μ'' μ0
  have : IsMulRightInvariant μ'' := by
    refine ⟨fun k => ?_⟩
    rw [hc, Measure.map_smul, map_mul_right_eq_self]
  exact us_invInv μ''

theorem invStab_of_finVol (hFV : FinVolStab) : InvStab := by
  intro F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ'' hμ''
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hcl := us_isClosed_stab F E σ M a J X0
  have : LocallyCompactSpace (stabT (AF F) σ J X0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : Countable (HFinIn (AF F) σ J) := um_countable_HFinIn F E σ M J
  let f : ratIn F E σ M J (stabT (AF F) σ J X0) → HFinIn (AF F) σ J := fun x =>
    ⟨((x : stabT (AF F) σ J X0) : HA (AF F) σ J),
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).1⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext e)
  have : Countable (ratIn F E σ M J (stabT (AF F) σ J X0)) := hinj.countable
  obtain ⟨𝓕, h𝓕⟩ :=
    exFDStab_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ'' hμ''
  have hfin := hFV F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ'' hμ'' 𝓕 h𝓕
  have : SigmaCompactSpace (stabT (AF F) σ J X0) :=
    um_sigmaCompact (ratIn F E σ M J (stabT (AF F) σ J X0)) μ'' 𝓕 h𝓕 hfin
  have : IsMulRightInvariant μ'' :=
    um_rightInv (ratIn F E σ M J (stabT (AF F) σ J X0)) μ'' 𝓕 h𝓕 hfin
  exact us_invInv μ''

end PI.VolStabS.InvariantStabilizerAssembly
