import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsPlacesSingleton
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeOfOddExponentSum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnderEqOfConj
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.DownPair

theorem pair_data : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), (∃ cA a, Defin R.θ (Vc D i) cA a) ∧ Places (Vc D i) (R.βV i) (R.Pg ∪ R.Q t) ∧ under (R.Pg ∪ R.Q t) = GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t ∧ GlobalTheory.LFun.UnrOff (F := D.host.F) (E := D.host.E) (chiV R i t) (↑(under (D := D) (R.Pg ∪ R.Q t))) ∧ (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) ∧ (Wc D i).SigOK ∧ (Wc D i).rank = D.R.r ∧ 0 < D.R.r ∧ (Vc D i).rank = D.R.r + D.R.t ∧ D.R.r + 5 ≤ D.R.t ∧ R.ΛV i = GlobalTheory.AdelicU.frameLat (Vc D i) ∧ R.ΛW i = GlobalTheory.AdelicU.frameLat (Wc D i) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t
  have hc := hG.core
  have hV := hc.lev.βV i
  have hW := hc.lev.βW i
  have hΛ : ∀ {V : Formalism.BasicNotions.HSpace D.host.E} {β Λ}, Formalism.IndefR.Links.IsSDFrame (D := D) V β Λ 1 → Λ = GlobalTheory.AdelicU.frameLat V := by
    intro V β Λ h
    obtain ⟨c, hf, -, -, h1, h2⟩ := h
    ext x
    rw [GlobalTheory.AdelicU.mem_frameLat]
    constructor
    · intro hx; have := h2 x hx; simp only [one_pow, Nat.cast_one, one_smul] at this; exact this
    · intro hx; simpa using h1 x hx
  have hΛV := hΛ hV
  have hΛW := hΛ hW
  have hEta : ∃ η, GlobalTheory.WeilParts.IsEtaTilde D η := by
    have hω := hc.thP.ωP i t
    refine ⟨R.eta, GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D R.eta R.C.eta hc.lev.eta R.C.isEta _ (Vc D i).rank (Wc D i).rank hω.resS hω.resT ?_⟩
    · rw [D.sp.V_rank _ (by omega) (by omega), D.sp.W_rank _ (by omega) (by omega)]
      unfold Formalism.BasicNotions.Ranks.nV
      have := D.R.t_odd
      obtain ⟨k, hk⟩ := this
      exact ⟨D.R.r + k, by omega⟩
  have hUnr : GlobalTheory.LFun.UnrOff (F := D.host.F) (E := D.host.E) (chiV R i t) (↑(under (D := D) (R.Pg ∪ R.Q t))) := by
    intro w hw
    have hgood : GlobalTheory.Hk3.Good R t w := by
      intro PP hPP
      constructor
      · rintro rfl
        exact hw (Finset.mem_coe.2 (Finset.mem_image.2 ⟨PP, Finset.mem_union.2 hPP, rfl⟩))
      · intro hcj
        exact hw (Finset.mem_coe.2 (Finset.mem_image.2 ⟨PP, Finset.mem_union.2 hPP, GlobalTheory.RawLift.Small.under_eq_of_conj hcj⟩))
    have hg := ((GlobalTheory.GoodPrimes.good_primes R F hc.lev).2.1 t w hgood).1
    have hnotover : ∀ k, ¬ Formalism.L2.Host.OverP D.host (D.host.g k) w := by
      intro k hk
      apply hg
      push_cast
      fin_cases k
      · exact Ideal.mul_mem_right _ _ hk
      · exact Ideal.mul_mem_left _ _ hk
    have hmu : (R.C.mu0 i).UnrAt w := (R.C.isMu0 i).unr w hnotover
    have hxi : (R.xiH t).UnrAt w := by
      by_contra h
      rcases (hc.lev.Q_ram t w).1 h with h1 | ⟨PP', h1, h2⟩
      · exact (hgood w (Or.inr h1)).1 rfl
      · exact (hgood PP' (Or.inr h1)).2 h2
    have heta : R.C.eta.UnrAt w := R.C.isEta.unr w
    have a1 := (GlobalTheory.LFun.unrAt_iff_of_chrEq (hc.lev.mu0 i) w).2 hmu
    have a2 := (GlobalTheory.LFun.unrAt_iff_of_chrEq (hc.lev.xi t) w).2 hxi
    have a3 := (GlobalTheory.LFun.unrAt_iff_of_chrEq hc.lev.eta w).2 heta
    exact (a1.mul a2).mul a3.inv
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  refine ⟨GlobalTheory.Core.Rk.Exh.Model.exists_defin hc.models.inf (D.sp.V_sig _) (hc.models.vpos i), ⟨?_, ?_, fun v h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2⟩, rfl, hUnr, hEta, D.sp.W_sig _, D.sp.W_rank _ (by omega) (by omega), hr, ?_, D.R.rank_add_five_le, hΛV, hΛW⟩
  · obtain ⟨c, hf, -⟩ := hV
    rw [← hΛV]; exact hf
  · obtain ⟨-, e, he, -⟩ := hc.thP.vP i t
    exact ⟨e, he⟩
  · rw [D.sp.V_rank _ (by omega) (by omega)]
    unfold Formalism.BasicNotions.Ranks.nV
    rfl

end GlobalTheory.DownPair
