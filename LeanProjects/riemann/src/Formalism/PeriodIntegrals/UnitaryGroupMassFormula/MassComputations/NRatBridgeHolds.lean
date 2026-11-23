import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NfinOfRatN

noncomputable section

open scoped TensorProduct
open Matrix NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

namespace MassDataMassesW

def NRatBridge : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (δ : X.B.I.GA),
    (toHA X.B.I hb δ ∈ (HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J :
        Subgroup (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)) ∧
      toHA X.B.I hb δ ∈ Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) ↔
    (δ ∈ X.B.I.GFset ∧ δ.1 ∈ X.NinfU u ∧ δ.2 ∈ X.NfinU u)

open NRatW in
theorem nRatBridge_holds : NRatBridge := by
  intro D X hb u δ
  obtain ⟨hinfB, hfinB⟩ := toHA_isBridge X.B.I hb δ
  constructor
  · rintro ⟨hF, hN⟩
    obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hF)
    have hmat : HA.mat (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (toHA X.B.I hb δ) =
        Formalism.UG.bc (inclR (AF X.B.I.F)) γ := hγe.symm
    have hM : ((HA.mat (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (toHA X.B.I hb δ) :
        GL (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) =
        (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (AF X.B.I.F)) := by
      rw [hmat]; rfl
    have hRat := ratN_of_AF X u _ _ hM hN
    have hinf : ∀ v, Formalism.MainNotions.S.uMat (δ.1 v) =
        (X.B.I.P v)⁻¹ * (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v :=
      fun v => (hinfB v).trans (ofHAInf_rat X.B.I _ γ hmat v)
    have hfin : X.B.I.fmat δ.2 =
        (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) :=
      hfinB.trans (ofHAFin_rat X.B.I _ γ hmat)
    exact ⟨⟨γ, hγ, hinf, hfin⟩, ninf_of_ratN X u _ δ.1 hinf hRat, nfin_of_ratN X u _ δ.2 hfin hRat⟩
  · rintro ⟨⟨γ, hγ, hinf, hfin⟩, -, hNf⟩
    have hRat := ratN_of_fin X u _ δ.2 hfin hNf
    have hU : Formalism.UG.bc (inclR (F := X.B.I.F) (E := X.B.I.E) (AF X.B.I.F)) γ ∈
        HR (AF X.B.I.F) X.B.I.cm.sig X.B.I.J := by
      have hγ' : Formalism.UG.cT (starRingEnd X.B.I.E) (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * X.B.I.J *
          (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J := hγ
      have e1 : Formalism.UG.cT (sigR (AF X.B.I.F) X.B.I.cm.sig)
          ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (AF X.B.I.F))) =
          (Formalism.UG.cT (starRingEnd X.B.I.E) (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)).map
            (inclR (AF X.B.I.F)) := by
        ext i j
        simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, sigR_inclR]
        rfl
      show Formalism.UG.cT (sigR (AF X.B.I.F) X.B.I.cm.sig)
          ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (AF X.B.I.F))) * JR (AF X.B.I.F) X.B.I.J *
          ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (AF X.B.I.F))) = JR (AF X.B.I.F) X.B.I.J
      rw [e1, JR, ← Matrix.map_mul, ← Matrix.map_mul, hγ']
    obtain ⟨h, hmat⟩ : ∃ h : HAd X.B.I, HA.mat (AF X.B.I.F) X.B.I.cm.sig X.B.I.J h =
        Formalism.UG.bc (inclR (AF X.B.I.F)) γ :=
      ⟨(⟨_, hU⟩ : HR (AF X.B.I.F) X.B.I.cm.sig X.B.I.J), rfl⟩
    have hq : (toHA X.B.I hb).symm h = δ := by
      obtain ⟨a1, a2⟩ := toHA_isBridge X.B.I hb ((toHA X.B.I hb).symm h)
      rw [ContinuousMulEquiv.apply_symm_apply] at a1 a2
      refine Prod.ext (funext fun v => ?_) ?_
      · exact Subtype.ext (Units.ext ((a1 v).trans ((ofHAInf_rat X.B.I h γ hmat v).trans (hinf v).symm)))
      · exact Subtype.ext (Units.ext (a2.trans ((ofHAFin_rat X.B.I h γ hmat).trans hfin.symm)))
    have hδ : toHA X.B.I hb δ = h := by
      rw [← hq]
      exact (toHA X.B.I hb).apply_symm_apply h
    rw [hδ]
    refine ⟨Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ, hγ, hmat.symm⟩), ?_⟩
    have hM : ((HA.mat (AF X.B.I.F) X.B.I.cm.sig X.B.I.J h :
        GL (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) =
        (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (AF X.B.I.F)) := by
      rw [hmat]; rfl
    exact nsub_of_ratN X u _ h hM hRat

end MassDataMassesW
