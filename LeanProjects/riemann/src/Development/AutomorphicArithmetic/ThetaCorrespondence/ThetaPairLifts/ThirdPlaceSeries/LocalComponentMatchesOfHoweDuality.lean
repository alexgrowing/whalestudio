import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralTwistStable
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftGeneralLinear
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIsotypicInnerNeZeroStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtRows
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitReferencePairOfTrivialMu
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsUnitarizableOfFiniteTypeOfLocalComponents
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MGoodRef
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MRecLawsH
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocGRankOne
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlIsRecrecLaws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepsum
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecLawsH
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
noncomputable section
noncomputable section
namespace UpperTheory.One.M
theorem localComponent_matches_of_howeDuality_alt (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible)
 (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {D : D7} {cf : CharFrame D}
    {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {Rw : RowSide D} (a : _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL D cf rep Rw) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (P : NG.AutRep D.host.E D.R.nV) (μ : D.naut.CG 1)
    (hμ : (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩) (s : SplitPlace D.host.E)
    (π : IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)))
    (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))) (hπ : IsLocS (n := D.R.nV) P.S s π)
    (hτ : IsLocS (rep σ).S s τ) (hU : IsUnitarisable τ.ρ)
    (hP : ThetaPair ((cf.mu0 ⟨j - 1, by omega⟩).loc s.w) τ.ρ
      (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (cf.eta.loc s.w))))
    (hgπ₀ : UpperTheory.Zero.LLC.Good (GlobalTheory.LocLanglands.cls π)) :
    D.nbc.locAU j (a.A.cls j h1 h2 P) s.w =
      D.naut.lpChar (D.naut.lpSum (Rw.locR σ s.w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ s.w))
        (D.naut.locG D.naut.etaTinv s.w) := by
  classical
  haveI := GlobalTheory.CuspRep.host_isCMField D.host
  have L : _root_.UpperTheory.One.M.RecLawsH (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w) := (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 s.w)).recLaws
  set χ := cf.mu0 ⟨j - 1, by omega⟩ with hχ
  have hμc : IsComp χ s.w (χ.loc s.w) := ⟨GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc χ s.w, fun _ => rfl⟩
  obtain ⟨ξ₀, -, huniq, hunit⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E χ s.w
  have hχu : χ.IsUnitary := hμ ▸ (a.chr.e1 μ).2
  have hμU : IsUnitaryChar (χ.loc s.w) := fun x => by
    rw [huniq _ hμc]; exact hunit hχu x
  have hηc : IsComp cf.eta s.w (cf.eta.loc s.w) := ⟨GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc cf.eta s.w, fun _ => rfl⟩
  have hηi : IsComp (a.chr.e1 D.naut.etaTinv).1 s.w ((cf.eta⁻¹).loc s.w) := by
    rw [a.chr.etaTinv]
    exact ⟨GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc _ s.w, fun _ => rfl⟩
  have hinv : (cf.eta⁻¹).loc s.w = (cf.eta.loc s.w)⁻¹ := MonoidHom.ext (HChar.loc_inv _ _)
  have hrt : D.R.r < D.R.t := by
    have := D.R.rank_add_five_le
    unfold Ranks.r
    omega
  let π₀ : Irr (s.w.adicCompletion D.host.E) (D.R.r + D.R.t) := Irr.ofIrrRep π
  let π' := GlobalTheory.SplitPairLift.twistIrr π₀ hηc.1
  let τ₀ : Irr (s.w.adicCompletion D.host.E) D.R.r := Irr.ofIrrRep τ
  let cμ := GlobalTheory.SplitPairLift.detIrr 1 hμc.1
  let τμ := GlobalTheory.SplitPairLift.detIrr D.R.t hμc.1
  let cη := Irr.ofDet 1 ((cf.eta⁻¹).loc s.w) hηi.1
  have e1 : Nonempty (π'.π.Equiv (prod₂ τ₀.π τμ.π)) :=
    _root_.GlobalTheory.T.theta_lift_general_linear hBZ hB _ D.R.r D.R.t _ _ _ τ.ρ π'.π hrt hμc.1 hμU τ.smooth τ.irr hU π'.smooth π'.irr hP
  have e2 := L.prod _ _ τ₀ τμ π' e1
  have e3 := L.det D.R.t _ cμ τμ ⟨.refl _⟩ ⟨.refl _⟩
  have hgπ : GoodI π' := by
    have e : GlobalTheory.LocLanglands.cls (⟨π'.V, π'.π, π'.smooth, π'.irr⟩ : IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E))) =
        (GlobalTheory.LocLanglands.cls (⟨π₀.V, π₀.π, π₀.smooth, π₀.irr⟩ : IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)))).tw (cf.eta.loc s.w) hηc.1 :=
      (GlobalTheory.LocGL.IrrGL.tw_of π₀.π π₀.smooth π₀.irr (cf.eta.loc s.w) hηc.1).symm
    show UpperTheory.Zero.LLC.Good _
    rw [e]
    exact (GlobalTheory.RecT.good_tw_iff _ _ _).2 hgπ₀
  have e4 := _root_.UpperTheory.One.M.RecLawsH.twist L _ (cf.eta.loc s.w)⁻¹ cη π' π₀ hgπ (by rw [← hinv]; exact ⟨.refl _⟩) (by
    show Nonempty (π₀.π.Equiv (GlobalTheory.SmGL.twist (GlobalTheory.SmGL.twist π₀.π (GlobalTheory.SmGL.detChar _ (cf.eta.loc s.w))) (GlobalTheory.SmGL.detChar _ (cf.eta.loc s.w)⁻¹)))
    rw [GlobalTheory.SplitPairLift.twist_twist_inv]
    exact ⟨.refl _⟩)
  have eμ := _root_.GlobalTheory.LiftSplitLoc.locG_rankOne_alt a.T a.cg a.chr μ s.w (χ.loc s.w) (hμ ▸ hμc)
  have eη := _root_.GlobalTheory.LiftSplitLoc.locG_rankOne_alt a.T a.cg a.chr D.naut.etaTinv s.w _ hηi
  have hau : a.T.e s.w (D.nbc.locAU j (a.A.cls j h1 h2 P) s.w) = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w _ π₀ := a.au j h1 h2 P s π hπ
  have hrow : a.T.e s.w (Rw.locR σ s.w) = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w _ τ₀ := a.row.1 σ s τ hτ
  have h7 : D.naut.lpDim (D.naut.locG D.naut.etaTinv s.w) = 1 := by
    rw [← a.T.dim, eη, L.dim]
  apply (a.T.e s.w).injective
  rw [a.T.char _ _ _ h7, a.T.sum, GlobalTheory.SplitPairLift.e_spehLoc, hau, hrow, e4, e2, e3, eη, eμ]
  rfl
set_option maxHeartbeats 1000000 in
theorem liftSplitLocal_of_howeDuality_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf _ Rw a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real, inner ℂ F (D.what₂.thetaT D.what₂.mu0 j y) ≠ 0) → ∀ μ : D.naut.CG 1, (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩ → ∀ w, IsSplitPl D.host w → D.nbc.locAU j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)) w = D.naut.lpChar (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)) (D.naut.locG D.naut.etaTinv w) := by
  intro hP hL
  have hA := _root_.GlobalTheory.T.split_reference_pair_of_trivial_mu_alt hP hL
  have hB := _root_.GlobalTheory.T.exists_unitarisable_local_component_at_split hP hL
  have hC := _root_.UpperTheory.One.M.goodRef_alt hP hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters at hA hB hC ⊢
  refine GlobalTheory.LiftRef.overRows_and_mono (GlobalTheory.LiftRef.overRows_and_mono hA hB fun _ _ _ _ _ _ _ _ _ _ _ a b => And.intro a b) hC fun K B f T w Z Wt hX z p0 Y HAB HC Rw a M tup Q hM hI j h1 h2 σ S hS hpair μ hμ v hv => ?_
  obtain ⟨HA, HB⟩ := HAB
  obtain ⟨s, rfl⟩ := GlobalTheory.PairReadPf.exists_splitPlace_w _ v hv
  have hne : (w.st Z).toD7.what₂.isot j σ ≠ ⊥ := by
    obtain ⟨y, hy, F, -, hF⟩ := hpair
    intro hb
    rw [hb, Submodule.mem_bot] at hy
    apply hF
    rw [hy, map_zero, inner_zero_right]
  obtain ⟨τ, hτ, hU⟩ := HB Rw a M tup Q hM hI j σ hne s
  obtain ⟨π, hπ⟩ := GlobalTheory.LocCompSplit.exists_isLocS (GlobalTheory.LiftRef.autOf (M _ j h1 h2) S hS) s
  have hne' : (NG.isoTyp (M _ j h1 h2).wt.ρ S).comap (M _ j h1 h2).real ≠ ⊥ := by
    obtain ⟨y, hy, F, hF, hF0⟩ := hpair
    intro hb
    rw [hb, Submodule.mem_bot] at hF
    subst hF
    exact hF0 (inner_zero_left _)
  exact _root_.UpperTheory.One.M.localComponent_matches_of_howeDuality_alt hP.what₂.bz hP.what₂.bern hL a j h1 h2 σ _ μ hμ s π τ hπ hτ hU
    (HA Rw a M tup Q hM hI j h1 h2 σ S hS hpair s π τ hπ hτ) (HC Rw a M tup Q hM hI j h1 h2 S hS hne' s π hπ)
end UpperTheory.One.M
end
end
end
