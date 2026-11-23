import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameInert
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterDefiniteUnitaryInertPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsThetaPull
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFacts

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Inert

theorem satEx : SatEx := by
  intro E _ _ _ n w hw b ϖ q hb hϖ hU σ ha hfix
  have hUL : UL n w = UJ (cj w) 1 := GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw n
  let a := GlobalTheory.UnitaryBC.SatEx.toAnti b hb.2
  have hac := GlobalTheory.UnitaryBC.SatEx.continuous_toAnti b hb.2
  let p : UL n w ≃* GU (cj w) n := (MulEquiv.subgroupCongr hUL).trans a
  have hp : ∀ x, (p x).1 = b⁻¹ * x.1 * b := fun x => rfl
  have hpc : Continuous p := hac.1.comp (continuous_subtype_val.subtype_mk _)
  have hpsc : Continuous p.symm := (continuous_subtype_val.comp hac.2).subtype_mk _
  let hh : UL n w ≃ₜ GU (cj w) n :=
    { toEquiv := p.toEquiv, continuous_toFun := hpc, continuous_invFun := hpsc }
  let σ' : SmIrr (GU (cj w) n) :=
    { V := σ.V
      ρ := σ.ρ.comp p.symm.toMonoidHom
      smooth := fun v => (σ.smooth v).preimage hpsc
      irred := GlobalTheory.ConjPairLoc.irred_comp _ _ p.symm.surjective σ.irred }
  have hfx : ∀ (K : Subgroup (GU (cj w) n)) (v : σ.V),
      v ∈ fixed σ'.ρ K ↔ v ∈ fixed σ.ρ (K.comap p.toMonoidHom) := by
    intro K v
    constructor
    · intro h
      refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_
      have h1 : σ.ρ (p.symm (p k)) v = v := GlobalTheory.LGrp.mem_fixed.1 h (p k) hk
      rwa [p.symm_apply_apply] at h1
    · intro h
      refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_
      have hk' : p.symm k ∈ K.comap p.toMonoidHom := by
        rw [Subgroup.mem_comap]
        simpa using hk
      exact GlobalTheory.LGrp.mem_fixed.1 h (p.symm k) hk'
  have ha' : IsAdmissible σ'.ρ := by
    refine ⟨σ'.smooth, fun K ho hc => ?_⟩
    have e : fixed σ'.ρ K = fixed σ.ρ (K.comap p.toMonoidHom) := Submodule.ext (hfx K)
    rw [e]
    exact ha.2 _ (ho.preimage hpc) (hh.isCompact_preimage.2 hc)
  have hs' : GlobalTheory.LGrp.IsSpherical σ'.ρ (KU (cj w) n) := by
    obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hfix
    refine (Submodule.ne_bot_iff _).2 ⟨v, (hfx _ v).2 (GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_), h0⟩
    have hk1 : (p k).1 ∈ GlobalTheory.LFun.KGL w n := (Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hk)).2
    have e : k.1 = b * (p k).1 * b⁻¹ := by rw [hp]; group
    have hk2 : k.1 ∈ GlobalTheory.LFun.KGL w n := by
      rw [e]
      exact mul_mem (mul_mem hb.1 hk1) (inv_mem hb.1)
    exact GlobalTheory.LGrp.mem_fixed.1 hv k (Subgroup.mem_subgroupOf.2 hk2)
  obtain ⟨α, hα⟩ := GlobalTheory.LFun.ExSatU.exists_hasSatU E w (ϖ : w.adicCompletion E) (cj w) q n hU σ'.V σ'.ρ
    σ'.irred ha' hs'
  have hcomp : σ'.ρ.comp p.toMonoidHom = σ.ρ := by
    ext g v
    show σ.ρ (p.symm (p g)) v = σ.ρ g v
    rw [p.symm_apply_apply]
  refine ⟨α, p, σ', hp, hα, ?_⟩
  rw [hcomp]
  exact ⟨Representation.Equiv.refl _⟩

end PositivityTheory.Rg.BcB.F.Inert

end
