import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPairThetaLowestStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsUnitarisableStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaCorrespondenceLargeRankStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

noncomputable section

namespace GlobalTheory.LiftSplitLoc

open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands in

theorem locG_rankOne {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (cg : CGTrue hL D T) (cs : CharSide D cf) (π : D.naut.CG 1) (w : PlE D.host)
    (ξ : (w.adicCompletion D.host.E)ˣ →* ℂˣ) (h : IsComp (cs.e1 π).1 w ξ) :
    T.e w (D.naut.locG π w) = rcAt hL D w 1 (Irr.ofDet 1 ξ h.1) := by
  haveI := host_isCMField D.host
  set χ' := (CGu.equivChar D.host.E (cg.e 1 π)).1 with hχ'
  set χ := (cs.e1 π).1 with hχ
  have hloc : ∀ v, T.e v (D.naut.locG π v) = ParLaws.locPar hL (CG.ofChar χ') (D.nd.plOm.2 v) := fun v => by
    rw [cg.loc, hχ', CGu.ofChar_equivChar]; rfl
  have unr' : ∀ v, D.naut.unr (D.naut.locG π v) ↔ χ'.UnrAt v := fun v => by
    rw [T.unr, hloc v]; exact GlobalTheory.RankOneComp.locPar_ofChar_unr_iff hL χ' _
  have hchar : χ' = χ := by
    rw [← mul_inv_eq_one]
    apply GlobalTheory.HeckeSplitRow.eq_one_of_split D.host
    filter_upwards [D.naut.locG_unr_ae π] with v hv _
    have u1 := (cs.unr_iff π v).1 hv
    have u2 := (unr' v).1 hv
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [HChar.loc_mul, HChar.loc_inv, u1 x hx, u2 x hx, inv_one, mul_one]
    · have hf := cs.frob π v u1
      have hf' : D.naut.frobEig (D.naut.locG π v) = {(((χ'.val v)⁻¹ : ℂˣ) : ℂ)} := by
        rw [T.frobEig _ _ hv, hloc v]; exact GlobalTheory.RankOneComp.locPar_ofChar_frob hL χ' _ u2
      rw [hf', Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
      rw [HChar.val_mul, HChar.val_inv, hf, mul_inv_cancel]
  have hcomp : IsComp χ w (χ.loc w) := ⟨ParLaws.isSmoothChar_loc χ w, fun _ => rfl⟩
  obtain ⟨ξ₀, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E χ w
  have hξ : ξ = χ.loc w := (huniq _ h).trans (huniq _ hcomp).symm
  subst hξ
  rw [hloc, ParLaws.locPar_ofChar, rcAt]
  rw [hchar]
  rfl

set_option maxHeartbeats 1000000 in

theorem read (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible)
    (hH : GlobalTheory.Published.HoweDualityGL) (hL : GlobalTheory.Published.LocalLanglandsGL) {D : D7} {cf : CharFrame D}
    {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {Rw : RowSide D} (a : ParIn hL D cf rep Rw) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (P : NG.AutRep D.host.E D.R.nV) (μ : D.naut.CG 1)
    (hμ : (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩) (s : SplitPlace D.host.E)
    (π : IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)))
    (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))) (hπ : IsLocS (n := D.R.nV) P.S s π)
    (hτ : IsLocS (rep σ).S s τ) (hU : IsUnitarisable τ.ρ)
    (hP : ThetaPair ((cf.mu0 ⟨j - 1, by omega⟩).loc s.w) τ.ρ
      (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (cf.eta.loc s.w)))) :
    D.nbc.locAU j (a.A.cls j h1 h2 P) s.w =
      D.naut.lpChar (D.naut.lpSum (Rw.locR σ s.w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ s.w))
        (D.naut.locG D.naut.etaTinv s.w) := by
  classical
  haveI := GlobalTheory.CuspRep.host_isCMField D.host
  have L : RecLaws (rcAt hL D s.w) := (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 s.w)).recLaws
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
    GlobalTheory.T.theta_correspondence_large_rank hBZ hB hH _ D.R.r D.R.t _ _ _ τ.ρ π'.π hrt hμc.1 hμU τ.smooth τ.irr hU π'.smooth π'.irr hP
  have e2 := L.prod _ _ τ₀ τμ π' e1
  have e3 := L.det D.R.t _ cμ τμ ⟨.refl _⟩ ⟨.refl _⟩
  have e4 := L.twist _ (cf.eta.loc s.w)⁻¹ cη π' π₀ (by rw [← hinv]; exact ⟨.refl _⟩) (by
    show Nonempty (π₀.π.Equiv (GlobalTheory.SmGL.twist (GlobalTheory.SmGL.twist π₀.π (GlobalTheory.SmGL.detChar _ (cf.eta.loc s.w))) (GlobalTheory.SmGL.detChar _ (cf.eta.loc s.w)⁻¹)))
    rw [GlobalTheory.SplitPairLift.twist_twist_inv]
    exact ⟨.refl _⟩)
  have eμ := locG_rankOne a.T a.cg a.chr μ s.w (χ.loc s.w) (hμ ▸ hμc)
  have eη := locG_rankOne a.T a.cg a.chr D.naut.etaTinv s.w _ hηi
  have hau : a.T.e s.w (D.nbc.locAU j (a.A.cls j h1 h2 P) s.w) = rcAt hL D s.w _ π₀ := a.au j h1 h2 P s π hπ
  have hrow : a.T.e s.w (Rw.locR σ s.w) = rcAt hL D s.w _ τ₀ := a.row.1 σ s τ hτ
  have h7 : D.naut.lpDim (D.naut.locG D.naut.etaTinv s.w) = 1 := by
    rw [← a.T.dim, eη, L.dim]
  apply (a.T.e s.w).injective
  rw [a.T.char _ _ _ h7, a.T.sum, GlobalTheory.SplitPairLift.e_spehLoc, hau, hrow, e4, e2, e3, eη, eμ]
  rfl

end GlobalTheory.LiftSplitLoc

namespace GlobalTheory.LiftSplitLoc

set_option maxHeartbeats 1000000 in

theorem main : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.LiftRef.AtRows hL fun D cf _ Rw a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real, inner ℂ F (D.what₂.thetaT D.what₂.mu0 j y) ≠ 0) → ∀ μ : D.naut.CG 1, (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩ → ∀ w, IsSplitPl D.host w → D.nbc.locAU j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)) w = D.naut.lpChar (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)) (D.naut.locG D.naut.etaTinv w) := by
  intro hP hL
  have hA := GlobalTheory.T.split_pair_theta_lowest hP hL
  have hB := GlobalTheory.T.local_components_unitarisable hP hL
  unfold GlobalTheory.LiftRef.AtRows at hA hB ⊢
  refine GlobalTheory.LiftRef.overRows_and_mono hA hB fun K B f T w Z Wt hX z p0 Y HA HB Rw a M tup Q hM hI j h1 h2 σ S hS hpair μ hμ v hv => ?_
  obtain ⟨s, rfl⟩ := GlobalTheory.PairReadPf.exists_splitPlace_w _ v hv
  have hne : (w.st Z).toD7.what₂.isot j σ ≠ ⊥ := by
    obtain ⟨y, hy, F, -, hF⟩ := hpair
    intro hb
    rw [hb, Submodule.mem_bot] at hy
    apply hF
    rw [hy, map_zero, inner_zero_right]
  obtain ⟨τ, hτ, hU⟩ := HB Rw a M tup Q hM hI j σ hne s
  obtain ⟨π, hπ⟩ := GlobalTheory.LocCompSplit.exists_isLocS (GlobalTheory.LiftRef.autOf (M _ j h1 h2) S hS) s
  exact read hP.what₂.bz hP.what₂.bern hP.what₂.howe hL a j h1 h2 σ _ μ hμ s π τ hπ hτ hU
    (HA Rw a M tup Q hM hI j h1 h2 σ S hS hpair s π τ hπ hτ)

end GlobalTheory.LiftSplitLoc

end
