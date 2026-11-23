import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoTypeSpaceMaximalCompact
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHasSatakeOfUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.SplitSatLoc
section Local
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
end Local
section Key
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
end Key
section Main
set_option maxHeartbeats 800000 in
theorem exists_locComp_hasSatake_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i) (sp : SplitPlace D.host.E), (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ B : Multiset ℂˣ, B.card = D.R.nV → ∀ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F ≠ 0 → (∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) F = GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E sp.w) D.R.nV B k • F) → ∃ (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E))) (α : Fin D.R.nV → ℂˣ), IsLocS (P.H.av.S i Q) sp σ ∧ GlobalTheory.SmGL.HasSatake σ.ρ α ∧ Finset.univ.val.map α = B := by
  intro _ hL D P i Q sp hJ B hB F hFiso hFty hF0 hFeig
  have hirr := P.H.av.irr i Q
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV
    ({ (P.M.loc i).wt with S := P.H.av.S i Q, irrS := hirr } : NG.AutRep D.host.E D.R.nV) sp
  have hσ' : IsLocS (P.H.av.S i Q) sp σ := hσ
  obtain ⟨c, T0, hc, hcL, -, -, -⟩ := hσ'
  have hFfix : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → NG.rt D.host.E D.R.nV κ F = F := by
    intro κ hκ ht
    have hJκ := ((hJ κ ht).1).2 hκ
    have h1 := hFty.2 ⟨κ, hJκ⟩
    rw [(hJ κ ht).2 hJκ] at h1
    simpa using h1
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.LocVec.main D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) hirr sp σ hσ c hc hcL
    (Formalism.UG.GLint (Fin D.R.nV) (sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring) 1
    (fun g hg => hg) (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ) F hFiso hF0
    (fun κ ht h => by
      rw [MonoidHom.one_apply, Units.val_one, one_smul]
      exact hFfix κ ((GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff sp ht).1 h) ht)
  have hufix : u ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL sp.w D.R.nV) := by
    refine GlobalTheory.LGrp.mem_fixed.2 fun A hA => ?_
    have hA' := (map_mem_KGL_iff hc hcL (Matrix.GeneralLinearGroup.map c.symm.toRingHom A)).1
      (by rw [map_map_symm]; exact hA)
    have := hu _ hA'
    rwa [map_map_symm, MonoidHom.one_apply, Units.val_one, one_smul] at this
  have hsph : GlobalTheory.SmGL.IsSpherical σ.ρ := by
    have : u ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO (sp.w.adicCompletion D.host.E) (Fin D.R.nV)) := by
      rw [GlobalTheory.HeckeEigConj.KO_eq_KGL D.host.E sp.w D.R.nV]; exact hufix
    exact (Submodule.ne_bot_iff _).2 ⟨u, this, hu0⟩
  have hR := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 sp.w)
  obtain ⟨α, hα⟩ := _root_.UpperTheory.One.M.exists_hasSatake_of_unr_alt hR ((_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical hR σ).2 hsph)
  have hSat := GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake D.host.E sp.w D.R.nV σ.V σ.ρ α hα
  obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc D.host.E D.R.nV sp
  have hspan := GlobalTheory.SpanLoc.main D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) hirr sp σ hσ c hc hcL hFiso
  rw [iSup_subtype'] at hspan
  have hFK : F ∈ GlobalTheory.PRep.fixed (locAct D.R.nV (P.M.loc i).wt.W sp c e) (GlobalTheory.LFun.KGL sp.w D.R.nV) := by
    refine GlobalTheory.LGrp.mem_fixed.2 fun A hA => ?_
    rw [locAct_apply]
    refine hFfix _ ((GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff sp (he1 _)).1 ?_) (he1 _)
    rw [he2]
    exact (map_mem_KGL_iff hc hcL _).1 (by rw [map_map_symm]; exact hA)
  have hspan' : F ∈ ⨆ T : {T : σ.V →ₗ[ℂ] (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) // (∀ v, T v ∈ NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {sp.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (sp.loc D.R.nV x)) v) = NG.rt D.host.E D.R.nV x (T v)}, LinearMap.range T.1 := hspan
  have hequiv : ∀ (T : {T : σ.V →ₗ[ℂ] (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) // (∀ v, T v ∈ NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {sp.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (sp.loc D.R.nV x)) v) = NG.rt D.host.E D.R.nV x (T v)}) g v, T.1 (σ.ρ g v) = locAct D.R.nV (P.M.loc i).wt.W sp c e g (T.1 v) := by
    intro T g v
    rw [locAct_apply, ← T.2.2 _ (he1 _) v, he2, map_map_symm]
  have hIs : GlobalTheory.LFun.IsSatVecGL sp.w (locAct D.R.nV (P.M.loc i).wt.W sp c e) F (Finset.univ.val.map α) :=
    GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup (ρ := locAct D.R.nV (P.M.loc i).wt.W sp c e) σ.irr hSat
      Subtype.val hequiv hspan' hFK hF0
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV (E := maximalRealSubfield D.host.E) sp.v
  have hϖ' : IsUnif D.host.E sp.v ϖ := hϖ
  have heq : ∀ k ≤ D.R.nV, GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E sp.w) D.R.nV (Finset.univ.val.map α) k =
      GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E sp.w) D.R.nV B k := by
    intro k hk
    have h1 := hIs.2.2.2 (c ϖ) (isUnifV_map hc hcL hϖ') k hk
    rw [← heckeD_eq_heckeVec sp c hc hcL e he1 he2 _ (fun κ ht => (hJ κ ht).1) hϖ' k hFfix, hFeig ϖ hϖ' k hk] at h1
    exact (smul_left_injective ℂ hF0 h1).symm
  exact ⟨σ, α, hσ, hα, GlobalTheory.LFun.eq_of_satEig_eq (GlobalTheory.LFun.qV_ne_zero sp.w) (by simp) hB heq⟩
end Main
end GlobalTheory.SplitSatLoc
end
end
