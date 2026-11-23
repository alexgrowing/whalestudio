import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.AdelRep
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PGrowth
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IntegrableCut
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.Count1
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialInfinitePlaceOfUnramified

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem trM_pt {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {l₁ : InfinitePlace E → DomWeight a}
    {l₂ : InfinitePlace E → DomWeight b} {D : Dom E a b} (A : Ar l₁ l₂ D) (S : Set (Pl E)) (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E)
    (φ₁ φ₂ : ∀ w : Pl E, LF a b w) (t : PT A.blk) (ht : t.ψ = rt u₁ u₂ (A.ff S φ₁ φ₂)) :
    trM t.Φ A.tw = A.blk.vol⁻¹ • adel S u₁ u₂ (t.arch (Tl l₁) (Tl l₂)) φ₁ φ₂ := by
  funext g
  have hT3 : F.trM t.Φ (opM (Tl l₁) (Tl l₂) (1 : Matrix Unit Unit ℂ)) g = _ :=
    tensTr E a b (Ml l₁) (Ml l₂) Unit t.ka t.kb (Tl l₁) (Tl l₂) t.ψ 1 g
  have hA : ∏ v, t.arch (Tl l₁) (Tl l₂) v (GeneralLinearGroup.map (cV v) g.1, GeneralLinearGroup.map (cV v) g.2) =
      (∏ v, phiOf (Ml l₁ v) (Tl l₁ v) (t.ka v) (gInf v g.1)) * ∏ v, phiOf (Ml l₂ v) (Tl l₂ v) (t.kb v) (gInf v g.2) := by
    simp only [PT.arch]
    exact Finset.prod_mul_distrib
  have hF : finFn S φ₁ φ₂ (hFin g * (ratF E a u₁, ratF E b u₂)⁻¹) =
      ∏ᶠ v ∈ S, φ₁ v (cpt v u₁ g.1, cpt v u₂ g.2) * if IsSplitAt v then φ₂ v (cpt' v u₁ g.1, cpt' v u₂ g.2) else 1 := by
    simp only [finFn, Adel.cpt_eq, Adel.cpt'_eq]
    rfl
  refine hT3.trans ?_
  rw [ht, Pi.smul_apply, smul_eq_mul, adel, hA, ← hF]
  simp only [F.rt, Ar.ff, Finset.univ_unique, Finset.sum_singleton, Matrix.one_apply_eq]
  ring

theorem cmbEll_of (hT : CmbTest) (hS : SeenFam) (hSl : PositionTest) (hL : LefL) (hF : FfAlg) : CmbEll := by
  intro E _ _ _ hU a b l₁ l₂ D A μ₁ μ₂ h₁ h₂
  haveI := GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace E hU
  haveI := A.ha
  haveI := A.hb
  haveI : BorelSpace (G a) := ⟨rfl⟩
  haveI : BorelSpace (G b) := ⟨rfl⟩
  haveI : BorelSpace (GA E a) := ⟨rfl⟩
  haveI : BorelSpace (GA E b) := ⟨rfl⟩
  obtain ⟨c, hc, h4⟩ := global_character_holds E hU a b μ₁ μ₂ A.μa A.μb
  by_cases hv : A.blk.vol = 0
  · exact ⟨1, one_ne_zero, fun S _ _ hS' => absurd hv (hF E a b l₁ l₂ D A S hS').1⟩
  refine ⟨A.blk.vol⁻¹ * c * 2 ^ ((a + b) * Fintype.card (InfinitePlace E)),
    mul_ne_zero (mul_ne_zero (inv_ne_zero hv) hc) (pow_ne_zero _ two_ne_zero), ?_⟩
  intro S Z L hSec hZ u₁ u₂ hu₁ hu₂ φ T e₁ e₂ k C R hφ hreg hIn hR hC
  obtain ⟨c₀, hc₀, ht⟩ := hT E a b l₁ l₂ D A S Z L hSec hZ u₁ u₂ hu₁ hu₂
  have ht' := (ht φ T _ _ C R hφ hreg hR hC).1
  have hr : 0 ≤ c₀ * (1 + R) := mul_nonneg hc₀ (by linarith)
  obtain ⟨-, hseen, htest, -⟩ := (hS E a b S Z L hZ φ T e₁ e₂ hφ hIn).2 k
  obtain ⟨hln, -, hsl⟩ := hSl E a b S Z L hZ
  have h3 := G3.g3 E hU a b S hSec l₁ l₂ _ htest (by
    obtain ⟨w, hw, hw'⟩ := hreg
    exact ⟨w, (hZ w hw).1, by rw [fam, if_pos hw]; exact hw'⟩)
  have one : ∀ j ∈ C.s, ellSum2 μ₁ μ₂ (trM (C.t j).Φ A.tw) =
      A.blk.vol⁻¹ * c * 2 ^ ((a + b) * Fintype.card (InfinitePlace E)) * (C.t j).val (chi l₁) (chi l₂) *
        geomSt2 S l₁ l₂ (fam Z T φ e₁ e₂ k) := fun j hj => by
    obtain ⟨ok, hψ, -, -⟩ := hC j hj
    have e := trM_pt A S u₁ u₂ _ _ (C.t j) hψ
    have e' : adel S u₁ u₂ ((C.t j).arch (Tl l₁) (Tl l₂)) (intersection_update_fsHerm_neg_one Z T φ fun w => (e₁ w).pow k)
        (intersection_update_fsHerm_neg_one Z T L.ln fun w => (e₂ w).pow k) = ∑ _i ∈ ({()} : Finset Unit), A.blk.vol • trM (C.t j).Φ A.tw := by
      rw [Finset.sum_singleton, e, smul_smul, mul_inv_cancel₀ hv, one_smul]
    have h5 := h4 S hSec u₁ u₂ hu₁ hu₂ l₁ l₂ (fun v => (C.t j).va v (chi l₁ v) * (C.t j).vb v (chi l₂ v))
      ((C.t j).arch (Tl l₁) (Tl l₂)) _ _
      (fun v => (hL E a b l₁ l₂ D A).2 v _ _ _ _ _ (ok.ka v) (ok.kb v)) ((hsl φ hφ).2 T fun w => (e₁ w).pow k)
      ((hsl _ hln).2 T fun w => (e₂ w).pow k)
    rw [e', ellLin_holds E a b μ₁ μ₂ Unit _ _ _ _ hr (fun _ _ => ht' j hj), Finset.sum_singleton, hseen, h3,
      Finset.prod_mul_distrib] at h5
    have hval : (C.t j).val (chi l₁) (chi l₂) = (∏ v, (C.t j).va v (chi l₁ v)) * ∏ v, (C.t j).vb v (chi l₂ v) := rfl
    rw [hval, ← inv_mul_cancel_left₀ hv (ellSum2 μ₁ μ₂ (trM (C.t j).Φ A.tw)), h5]
    ring
  rw [Cmb.Φ, Growth.trM_sum, ellLin_holds E a b μ₁ μ₂ _ _ _ _ _ hr ht', Cmb.val, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [one j hj]
  ring

end UpperTheory.Zero.ConvolutionTheory.EB
