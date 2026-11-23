import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DivisibleGroupTowerCompatibility
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspReadTOfCuspRead
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsLocEqOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsComplementaryProductAbsPow

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.DefiniteBC GlobalTheory.RowTie

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DefiniteBC.GoodModel

attribute [local instance] host_isCMField

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem cuspReadG_iff_cuspReadT (rc : RecMap A) : CuspReadG rc ↔ GlobalTheory.RecT.CuspReadT rc := by
  refine ⟨fun h a P ha hc hg => h a P ha hc fun w σ hσ => ?_, fun h a P ha hc hg => h a P ha hc fun w => ?_⟩
  · obtain ⟨σ', hσ', hg'⟩ := hg w
    have e := (ParLawsT.cls_loc_eq_of_isLocComp hσ).symm.trans (ParLawsT.cls_loc_eq_of_isLocComp hσ')
    change UpperTheory.Zero.LLC.Good (cls (ParLaws.toRep σ))
    rw [e]; exact hg'
  · obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL H.E a P w
    exact ⟨σ, hσ, hg w σ hσ⟩

theorem cuspReadG_of_cgTrueT (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : WDTie D.nd D.naut)
    (C : GlobalTheory.HeightCounting.CGTrueT hT D T) :
    CuspReadG (GlobalTheory.RecT.recMapT T fun h => ParLawsT.locRecT hT h) := by
  rw [cuspReadG_iff_cuspReadT]
  exact GlobalTheory.RecT.cuspReadT_recMapT _ D T
    { isRecT := fun w => (GlobalTheory.RecT.isRecT_iff _).2 (ParLawsT.isRecT_locRecT hT _)
      e := C.e
      surj := C.surj
      zero := C.zero
      loc := fun a π w _ => C.loc a π w
      tw := C.tw
      inf := C.inf
      csd := C.csd }

theorem cuspReadG_of_family (rc : GlobalTheory.RecT.RecFam) (D : D7) (T : WDTie D.nd D.naut) (C : GlobalTheory.RecT.CGTrueT rc D T) :
    CuspReadG (GlobalTheory.RecT.recMapT T rc) :=
  (cuspReadG_iff_cuspReadT _).2 (GlobalTheory.RecT.cuspReadT_recMapT rc D T C)

theorem good_rank_one {w : PlE H} (σ : LocIrr w 1) : UpperTheory.Zero.LLC.Good (IrrGL.of σ.ρ σ.smooth σ.irred) := by
  have hc : (IrrGL.of σ.ρ σ.smooth σ.irred).IsCusp :=
    IrrGL.isCusp_of.2 ⟨one_pos, GlobalTheory.GenericUnitary.isCuspidal_of_isSmooth_one σ.smooth⟩
  refine ⟨_, hasSupport_self hc, fun y hy => ?_⟩
  left; rw [Multiset.mem_singleton.1 hy]; rfl

theorem rank_one {rc : RecMap A} (h : CuspReadG rc) (P : CuspSub H.E 1) (hc : P.IsCsd) :
    ∃ π : A.CG 1, A.csd π ∧ (∀ w σ, P.IsLocComp w σ → A.locG π w = rc w 1 σ) ∧
      ∀ τ m, P.HasInfChar τ m → A.infG π τ = m :=
  h 1 P le_rfl hc fun _ σ _ => good_rank_one σ

theorem isCsd_triv : (CuspSub.triv H.E (le_refl 1)).IsCsd := by
  refine ⟨LinearEquiv.refl ℂ _, fun o φ => Subtype.ext ?_⟩
  obtain ⟨φ, hφ⟩ := φ
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
  change act (thetaOp o) (c • oneFn H.E 1) = act o (c • oneFn H.E 1)
  rw [map_smul, map_smul, act_oneFn, act_oneFn]
  cases o <;> rfl

theorem exists_member {rc : RecMap A} (h : CuspReadG rc) :
    ∃ π : A.CG 1, A.csd π ∧ ∀ w, ∃ σ, (CuspSub.triv H.E (le_refl 1)).IsLocComp w σ ∧ A.locG π w = rc w 1 σ := by
  obtain ⟨π, h1, h2, -⟩ := rank_one h _ isCsd_triv
  refine ⟨π, h1, fun w => ?_⟩
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL H.E 1 (CuspSub.triv H.E (le_refl 1)) w
  exact ⟨σ, hσ, h2 w σ hσ⟩

theorem not_cuspReadG (rc : RecMap A) (h : ∀ π : A.CG 1, ¬ A.csd π) : ¬ CuspReadG rc := fun hr =>
  let ⟨π, h1, _⟩ := exists_member hr
  h π h1

end GlobalTheory.DefiniteBC.GoodModel

end
