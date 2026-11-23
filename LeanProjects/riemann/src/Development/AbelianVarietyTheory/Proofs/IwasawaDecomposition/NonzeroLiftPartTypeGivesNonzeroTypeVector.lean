import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotInDetectByEqvMap
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.IsotPartVec

attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem actM_of_mult {D : D7} {V : HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
    {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (P : principalLevelFrame.RowPsi V n) (M : Mult.DSModel V Sp)
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : Mult.MMap M} (hT : T ∈ Mult.Mult θ M J χ)
    (κ : Formalism.AUTREP.GAf D.host.E n) (hκ : P.ψ κ ∈ J) : principalLevelFrame.actM P M κ T = χ (P.ψ κ) • T := by
  apply MultilinearMap.ext
  intro v
  funext g
  rw [principalLevelFrame.actM_apply, principalLevelFrame.mult_lev hT v _ hκ g]
  rfl

theorem exists_typeVec_of_isotL {D : D7} {V : HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (P : principalLevelFrame.RowPsi V n) (M : Mult.DSModel V Sp)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (π : Formalism.L2.NG.FinTyp D.host.E n)
    (h : principalLevelFrame.isotL θ P M J χ e π ≠ ⊥) :
    ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec (P.ψ ⁻¹' J) (fun κ => χ (P.ψ κ)) x := by
  obtain ⟨T, hT, hT0⟩ := (Submodule.ne_bot_iff _).1 h
  have hTg : T ∈ Mult.goodPart θ M J χ e := (Submodule.mem_inf.1 hT).1
  have hTi : T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π := (Submodule.mem_inf.1 hT).2
  have hTm : T ∈ Mult.Mult θ M J χ := (Submodule.mem_inf.1 hTg).1
  obtain ⟨q, hq0, hq⟩ := GlobalTheory.isotIn_detect_by_eqv_map D (Mult.MMap M) (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π T hTi hT0
  refine ⟨q T, (hq T hTi).1, hq0, fun κ hκ => ?_⟩
  rw [← (hq T hTi).2 κ, actM_of_mult P M hTm κ hκ, map_smul]

theorem main : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (π : Formalism.L2.NG.FinTyp D.host.E D.R.r) (i : Fin D.R.m), principalLevelFrame.isotL R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.toRealDat.eWf i (sg0 D A3.A)) π ≠ ⊥ → ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec ((Y.PW i).ψ ⁻¹' (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))) (fun κ => (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) ((Y.PW i).ψ κ)) x := by
  intro _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y _ _ π i h
  exact exists_typeVec_of_isotL _ _ _ _ _ _ π h

end GlobalTheory.IsotPartVec
