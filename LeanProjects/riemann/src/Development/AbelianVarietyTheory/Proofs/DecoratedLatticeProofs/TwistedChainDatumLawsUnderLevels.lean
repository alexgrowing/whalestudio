import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSplittingCharactersResidueUnramifi

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ChainTw.TwLaw
variable {D : D7}

theorem levChi_flag (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank)
    (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (κ : GA D V) :
    Lev.levChi V β (Lev.flagL (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B)) κ =
      Lev.levChi V β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B) κ := by
  unfold Lev.levChi levFn
  congr 3
  simp only [Lev.flagL, Lev.withP, Lev.datY, LevelP.full, LevelP.triv, if_true]
  exact (Lev.subgroupCharExtension_one_apply _ _).trans (Lev.subgroupCharExtension_one_apply _ _).symm

theorem lift_one_of_mem (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank)
    (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (κ : GA D V) (hκ : κ ∈ Lev.levG V β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B)) :
    Lev.IsLevelLift V β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B) 1 κ := by
  refine ⟨(Subgroup.mem_inf.1 hκ).1, hκ.2.1, ?_⟩
  have h2 := hκ.2.2
  simp only [Lev.datY, LevelP.triv, if_true] at h2
  exact Subgroup.mem_bot.1 h2

theorem lift_one_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    Lev.IsLevelLift V β L 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

theorem levChi_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    Lev.levChi V β L 1 = 1 := by
  unfold Lev.levChi
  rw [map_one]
  have : levFn β L 1 = 1 := (levChar D.sp.cm V.gram β L).map_one
  rw [this, Units.val_one]

set_option maxHeartbeats 1000000 in
open Classical in

theorem vecLawQ (D : D7) (c : Com D) (w : Twist D) (hw : w.Is c) (k : ℕ) (hk : k < D.R.m) (s s' : PiLocalization₂ D)
    (hs : IsStage c w k s) (hs' : IsStage c w (k + 1) s') (p : Step c s s') (hp : IsStep w (k + 1) p) :
    VecLaw p.ω (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) (Lev.levG s'.V s'.β s'.L)
      (fun κ => (Lev.levChi s'.V s'.β s'.L κ)⁻¹) p.f := by
  obtain ⟨hr, hL, hfs⟩ := hs
  obtain ⟨hr', hL', hfs'⟩ := hs'
  obtain ⟨f₀, hv⟩ := hp.vec
  obtain ⟨hres, uS, uT⟩ := GlobalTheory.ChainOnto.levRes_step D c hw.com k hk
  rw [hw.union] at hres uS uT
  have hG : ∀ PP ∈ w.Pg, GlobalTheory.StepLaw.ResAt (c.chS (k + 1)) PP (w.chi (k + 1) PP)⁻¹ ∧
      GlobalTheory.StepLaw.ResAt (c.chT (k + 1)) PP (w.chi (k + 1) PP)⁻¹ := fun PP hP => by
    rw [← hw.chiPg (k + 1) PP hP]; exact hres PP (Finset.mem_union_left _ hP)
  have hQ : ∀ PP ∈ w.Q, GlobalTheory.StepLaw.ResAt (c.chS (k + 1)) PP (w.ξ PP) ∧
      GlobalTheory.StepLaw.ResAt (c.chT (k + 1)) PP (w.ξ PP) := fun PP hP => by
    have := hres PP (Finset.mem_union_right _ hP)
    rwa [hw.chiQ (k + 1) PP hP, inv_inv] at this
  rw [hL] at hv
  have ea : s.V.rank = D.R.r + k * D.R.t := hfs.rank
  have eb : s'.V.rank = D.R.r + (k + 1) * D.R.t := hfs'.rank
  have law := fun {g0 : G0 w.Pg D.R.r} {g : GA D s.V} {h : GA D s'.V} =>
    @GlobalTheory.StepVecLaw.step_law D c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β f₀ p.f
      hp.weil hfs.sigOK hfs'.sigOK (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M) (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M)
      hfs.selfDual hfs'.selfDual hfs.frame hfs'.frame D.R.r D.R.t k hr hr' ea eb w.Pg w.Q hw.disj w.chi w.ξ hv hG hQ uS uT g0 g h
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · rw [hL] at hκ ⊢
    have h1 := law (lift_one_of_mem _ _ _ _ _ _ _ _ _ _ κ hκ) (lift_one_one _ _ _)
    rw [levChi_flag, levChi_flag, levChi_one, inv_one, one_smul] at h1
    have hne : Lev.levChi s.V s.β (Lev.datY s.V.rank D.R.r D.R.t k hr w.Pg w.Q (LevelP.triv w.Pg D.R.r ℂ) w.chi w.ξ Lev.Frm.B) κ ≠ 0 := by
      unfold Lev.levChi; exact Units.ne_zero _
    exact (inv_smul_eq_iff₀ hne).1 h1
  · rw [hL'] at hκ ⊢
    have h1 := law (lift_one_one _ _ _) (lift_one_of_mem _ _ _ _ _ _ _ _ _ _ κ hκ)
    rw [levChi_flag, levChi_flag, levChi_one, inv_one, one_smul] at h1
    exact h1

theorem levelLawQ : ∀ D : D7, LevelLawQ D := by
  intro D _ c w hw k hk s s' hs hs' p hp φ
  obtain ⟨h1, h2⟩ := vecLawQ D c w hw k hk s s' hs hs' p hp
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite c.ψ c.θ s.V s'.V _ _ p.ω hw.com.inf hp.weil _ _ _ _ p.f hp.theta
      κ (Subgroup.mem_inf.1 hκ).1 1 (one_mem _) _ (h1 κ hκ) φ
  · exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite c.ψ c.θ s.V s'.V _ _ p.ω hw.com.inf hp.weil _ _ _ _ p.f hp.theta
      1 (one_mem _) κ (Subgroup.mem_inf.1 hκ).1 _ (h2 κ hκ) φ

end GlobalTheory.ChainTw.TwLaw

end
