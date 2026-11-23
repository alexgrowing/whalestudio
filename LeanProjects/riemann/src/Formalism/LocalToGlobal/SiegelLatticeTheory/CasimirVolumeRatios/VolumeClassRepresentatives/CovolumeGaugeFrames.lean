import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.ZsCovTie
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.ZsCovR
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.UnfoldingBorel
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeCdPf

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.StandardLattice

namespace Formalism.L2.S.S7.CovolumeGaugeFrames

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem covolume_gauge_of_frames (hB : Formalism.L2.SG.LitS.BorelClassFinite)
    (hGD : ∀ (n : ℕ) (ε : Fin n → Bool), Gauge.GaugeDens ε) (hMR : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.MassRatioStd)
    (hVU : ∀ n, Gauge.VolUn n) :
    ∀ (X : CData) (n₀ : ℕ) (A C cb : ℝ), 8 ≤ n₀ → X.HypC n₀ A C cb →
      (∃ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (P Q : ℕ),
        X.I = Formalism.IndefR.Eqv.UI.instV fr ∧ fr.Λ = Formalism.IndefR.Eqv.UI.Lv D V ∧
        (∀ v, (Finset.univ.filter fun i => fr.ε v i = true).card = P) ∧ V.SigOK ∧ (∀ τ, V.sig τ = (P, Q)) ∧
        VolTie D ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep D ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt D V.rank ∧ cdScaleTie D) →
      Formalism.MainNotions.BridgeVolRatio.GaugeVolumeBoundVar X (ZsCovR.CasimirBaseCount : ℝ) := by
  intro X n₀ A C cb hn hX hT
  obtain ⟨D, V, fr, P, Q, hXI, hΛ, hε, hV, hs, hTie, hI, hC, hcd⟩ := hT
  exact Formalism.MainNotions.FundamentalDomainUnfolding.gauge_volume_bound_of_parts (Formalism.L2.S.S7.UnfoldingBorel.UnfoldVol_of_borel hB) hGD X hX.1
    (ZsCovR.covolR_nonneg X)
    (ZsCovTie.covolSum_of_tie fr X hXI hΛ hV hs hε hTie hI hC hcd
      (fun v => Formalism.MainNotions.S.Gauge.complex_gauge_normalization D hcd _ _) (hVU _))
    (ZsCovR.covolR_le hMR X hX.1 (by have := hX.1.1.1; omega))

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem volRatio_of_tiesFr (hB : Formalism.L2.SG.LitS.BorelClassFinite)
    (hGD : ∀ (n : ℕ) (ε : Fin n → Bool), Gauge.GaugeDens ε) (hMR : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.MassRatioStd)
    (hVU : ∀ n, Gauge.VolUn n) :
    ∃ Cv : ℝ, 1 ≤ Cv ∧ ∀ (X : CData) (n₀ : ℕ) (A C cb : ℝ), 8 ≤ n₀ → X.HypC n₀ A C cb → 1 ≤ X.qq →
      (∃ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (P Q : ℕ),
        X.I = Formalism.IndefR.Eqv.UI.instV fr ∧ fr.Λ = Formalism.IndefR.Eqv.UI.Lv D V ∧
        (∀ v, (Finset.univ.filter fun i => fr.ε v i = true).card = P) ∧ V.SigOK ∧ (∀ τ, V.sig τ = (P, Q)) ∧
        VolTie D ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep D ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt D V.rank ∧ cdScaleTie D) →
      Formalism.MainNotions.BridgeDeepQ.VolRatio X Cv :=
  ⟨(ZsCovR.CasimirBaseCount : ℝ) + 2, by have : (0 : ℝ) ≤ ZsCovR.CasimirBaseCount := Nat.cast_nonneg _; linarith,
    fun X n₀ A C cb hn hX _ hT => Formalism.MainNotions.BridgeVolRatio.vol_ratio_of_gauge_volume hGD X (le_trans (by norm_num) hn) hX.1
      (covolume_gauge_of_frames hB hGD hMR hVU X n₀ A C cb hn hX hT)⟩

end Formalism.L2.S.S7.CovolumeGaugeFrames
