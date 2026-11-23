import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateRowPairingPoincareSeriesBesselPeriodsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjRowEqTranslatedEvaluationCuspFormMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ModelIdentificationRespectsRealAndFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem poincare_eq_zero_of_per_vanish : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (Y : Formalism.L2.SG.Full.Full X) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)), S = parB (Ptw D) 0 → IsInfFam θ → IsStdChar D ψ (-1) → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → InHH X u Y.hK → ∀ T : Cu X u Y.hK, (∀ G ∈ MultT θ M J χ, ∀ ξ x, B.lev.per ψ (B.colForm T.1 ξ) (rTrans ((iotaX X h).symm (1, X.xu u) * t) (G x)) = 0) → PuFun X u Y.hK (Y.Dt u) T = 0 := by
  intro hDS hCR D X h u ψ A B Y θ S M J χ t hS hθ hψ hgap hE hM hHH T hper
  set P := PuFun X u Y.hK (Y.Dt u) T with hP
  have hPmem : P ∈ HHX X := ⟨P, (hHH T (Y.Dt u) (Y.reps u)).2.2.2⟩
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.Core.Mi.exists_conjVec hDS D X h θ S M hS hθ hgap hE
  have hss : star (star P) ∈ HHX X := by simpa using hPmem
  obtain ⟨G, hG, hae⟩ := GlobalTheory.Core.SeeOnto.see_onto hDS D X h θ S M J χ t v₀ hS hθ hgap hE hM hv₀ (star P) hss
  have hrow := (GlobalTheory.Core.Mi.rowFun_evS hCR D X h θ S M J χ t hθ hM G hG (PiTensorProduct.tprod ℂ v₀)).1
  obtain ⟨c, hc⟩ := GlobalTheory.T.conjugateRow_pairing_poincareSeries_besselPeriods D X h u ψ A B Y hψ hHH
  have hsplit := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h θ hθ hE
  have key := hc T _ (star P) hrow hae
  have ht1 : (iotaX X h t).1 = 1 := (hsplit.1 t).1 hM.1
  have hint : ∀ y, B.lev.per ψ (B.colForm T.1 (X.Wu u y))
      (fun g => evS X h t (G (PiTensorProduct.tprod ℂ v₀)) (iotaX X h g * (y, X.xu u))) = 0 := by
    intro y
    have hg₀ : (iotaX X h).symm (y, 1) ∈ GinfC (D.sp.Y 0) := (hsplit.2.1 _).2 (by simp)
    obtain ⟨σ, hσ⟩ := GlobalTheory.RealTransSm.rTrans_eq_map D θ (D.sp.Y 0) S M hθ _ hg₀
    have hfun : (fun g => evS X h t (G (PiTensorProduct.tprod ℂ v₀)) (iotaX X h g * (y, X.xu u))) =
        rTrans ((iotaX X h).symm (1, X.xu u) * t) (G (σ (PiTensorProduct.tprod ℂ v₀))) := by
      funext g
      rw [hσ J χ G hG]
      show G (PiTensorProduct.tprod ℂ v₀) ((iotaX X h).symm (iotaX X h g * (y, X.xu u)) * t) =
        G (PiTensorProduct.tprod ℂ v₀) (g * ((iotaX X h).symm (1, X.xu u) * t) * (iotaX X h).symm (y, 1))
      refine congrArg (G (PiTensorProduct.tprod ℂ v₀)) ?_
      apply (iotaX X h).injective
      simp only [map_mul, ContinuousMulEquiv.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_mul, ht1, mul_one]
      · simp only [Prod.snd_mul, mul_one, mul_assoc]
    rw [hfun]
    exact hper G hG _ _
  simp only [hint, MeasureTheory.integral_zero, mul_zero, star_star] at key
  exact inner_self_eq_zero.mp key

end GlobalTheory.Core.Mi
