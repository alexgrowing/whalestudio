import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulHalf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceSchwartzBruhatActsAsSupportedCombinatiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

noncomputable section

namespace GlobalTheory.FinPl.Rebase

theorem rebase : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS MS : Lat S) (LT MT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC S MS → IsSelfDualC T MT → (∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat MS ΛS → β.IsLat MT ΛT → ∀ f₀ g, Over ψ α β LS LT f₀ (latInd ΛS ΛT) g → Vac ψ S T MS MT (· = p.v) g ∧ ∀ Ψ f, Over ψ α β LS LT f₀ Ψ f → Over ψ α β MS MT g Ψ f) ∧ ∀ Ψ ∈ SB (Matrix n n' k), ∃ c : WO S T →₀ ℂ, CombAt (· = p.v) c ∧ ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → Over ψ α β LS LT f₀ Ψ (comb ψ S T c f₀) := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ hU S T α β LS MS LT MT hLS hLT hMS hMT
  have hOB := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hψ S T α β
  refine ⟨fun ΛS ΛT hΛS hΛT f₀ g hg => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨-, -, hvac0, -, ⟨Tm, hTm⟩, hall⟩ := id hg
    have hE := GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p n n' S T α β MS MT hMS hMT hU ΛS ΛT hΛS hΛT
    have hgT : g = Tm (halfInd p.e (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v))) := by
      rw [← hE]; exact hall Tm hTm
    have hmono := sbHalf_mono D k p S T LS MS LT MT hLS hLT hMS hMT
    have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e
        (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v)) 1 g Tm := by
      refine ⟨fun Φ hΦ x hx => hTm.trans Φ (hmono Φ hΦ) x hx, fun Φ hΦ y hy => hTm.modul Φ (hmono Φ hΦ) y hy, ?_⟩
      rw [one_smul, hgT]
    have hth : IsThetaFunO ψ S T g := ((hOB LS LT hLS hLT f₀ hvac0).2.1 _ g hg).1
    have hvacg : Vac ψ S T MS MT (· = p.v) g := by
      refine ⟨hth, ?_⟩
      rw [hgT]
      exact latVac_image D k p ψ hψ S T LS MS LT MT hLS hLT hMS hMT f₀ Tm hTm
    refine ⟨hvacg, fun Ψ f hf => ?_⟩
    obtain ⟨f', hf', -⟩ := (hOB MS MT hMS hMT g hvacg).1 Ψ hf.2.2.2.1
    have e1 : f' = Tm (extFun α β Ψ) := hf'.2.2.2.2.2 Tm hTm'
    have e2 : f = Tm (extFun α β Ψ) := hf.2.2.2.2.2 Tm hTm
    refine ⟨hMS, hMT, hvacg, hf.2.2.2.1, ⟨Tm, hTm'⟩, fun T' hT' => ?_⟩
    rw [e2, ← e1]
    exact hf'.2.2.2.2.2 T' hT'
  · obtain ⟨c, hc, hcomb⟩ := GlobalTheory.T.splitPlaceSchwartzBruhat_acts_as_supported_combination D k p n n' ψ hψ S T α β LS LT hLS hLT Ψ hΨ
    refine ⟨c, hc, fun f₀ hvac => ?_⟩
    obtain ⟨f, hf, -⟩ := (hOB LS LT hLS hLT f₀ hvac).1 Ψ hΨ
    exact ⟨hLS, hLT, hvac, hΨ, hf.2.2.2.2.1, fun T' hT' => (hcomb f₀ T' hT').symm⟩

end GlobalTheory.FinPl.Rebase

end
