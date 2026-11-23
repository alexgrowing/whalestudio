import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelOfLinks
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NotMemQBase
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamAllQ
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
theorem rel_of_links_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (d : _root_.GlobalTheory.MiTop.BottomData W u), (∀ t, (f.t t).Is) → MainX f.t → _root_.GlobalTheory.MiTop.LinkVanishes f d → _root_.GlobalTheory.MiTop.LinkTailCondition f → _root_.GlobalTheory.MiTop.LinkDescends f → _root_.GlobalTheory.MiTop.LinkSurjective f → _root_.GlobalTheory.MiTop.LinkCommutes f → _root_.GlobalTheory.MiTop.FamilyRatioCondition f → _root_.GlobalTheory.MiTop.FamilyServedCondition W → ∃ (U : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u) (r : ℝ) (c : W.P.T → ℂ), 0 < r ∧ (∀ φ, ‖U φ‖ = r * ‖φ‖) ∧ _root_.GlobalTheory.MiTop.UnitCoefficients W c ∧ d.Rel U c := by
  intro D L hT Gi Gl Kc Yd cX ex W u f d hIs hMain hZ hTail hDown hOnto hComm hRat hServ
  obtain ⟨a, ha⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  obtain ⟨n, hn⟩ : ∃ n, 2 * n + 2 = D.R.m := ⟨a - 1, by omega⟩
  have h : 2 * n + 2 * 0 + 2 = D.R.m := by omega
  have h₀ : 0 + 2 * n + 2 = D.R.m := by omega
  have hN : 2 * (n + 1) = D.R.m := by omega
  obtain ⟨S, r, s, hr, hS, hs, hcomm⟩ := hComm (n + 1) hN
  have hBot : ∀ t, (f.t t).cBot ≠ 0 := fun t =>
    Finset.prod_ne_zero_iff.mpr (fun j hj => (hIs t).cI j (Finset.mem_range.mp hj))
  have hTop : ∀ t, (f.t t).cTop (n + 1) ≠ 0 := fun t => (hRat (n + 1) hN t).1
  refine ⟨(S.symm : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u), r⁻¹, fun t => (f.t t).cTop (n + 1) * s / (f.t t).cBot,
    inv_pos.mpr hr, ?_, ?_, ?_⟩
  · intro φ
    have e := hS (S.symm φ)
    simp only [LinearEquiv.apply_symm_apply] at e
    simp only [LinearEquiv.coe_coe]
    rw [e, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  · refine ⟨fun t => div_ne_zero (mul_ne_zero (hTop t) hs) (hBot t), ?_⟩
    intro w k hk
    refine GlobalTheory.T.valuation_eq_zero_of_rootOfSUnitRatio D.what₂.LL D.what₂.embLL w (_root_.GlobalTheory.MiTop.qPrime_alt W (W.Q.Rl.mu w)) _ _ (hRat (n + 1) hN (W.Q.Rl.mu w)).2
      (fun p hp hb => hServ w p hp hb) k ?_
    rw [hk]
    have a1 := hTop (W.Q.Rl.mu w)
    have a2 := hTop W.P.A3.A.μ0
    have b1 := hBot (W.Q.Rl.mu w)
    have b2 := hBot W.P.A3.A.μ0
    field_simp
  · intro T hT0
    obtain ⟨G₀, hG₀⟩ := hOnto n h T hT0
    refine ⟨fun φ₀ => (f.t W.P.A3.A.μ0).cTop (n + 1) * (f.t W.P.A3.A.μ0).tail (2 * (n + 1)) hN
      ((f.t W.P.A3.A.μ0).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f W.P.A3.A.μ0 (S.symm φ₀))) G₀ / (f.t W.P.A3.A.μ0).cBot, ?_⟩
    intro φ₀ φ t F F' hFF α α' hrel y v
    obtain ⟨G, hG1, hGd⟩ := hDown n h t F'
    let sB : Bool → W.P.T := fun b => Bool.rec t W.P.A3.A.μ0 b
    let xB : Bool → D.what₂.Mu u := fun b => Bool.rec (S.symm φ) (S.symm φ₀) b
    let aB : Bool → ℂ := fun b => Bool.rec (α' / (f.t t).cBot) (α / (f.t W.P.A3.A.μ0).cBot) b
    let FB : ∀ b, (f.t (sB b)).CT := fun b => Bool.rec (motive := fun b => (f.t (sB b)).CT) G G₀ b
    have key := hMain n h h₀ Bool sB aB (fun b => _root_.GlobalTheory.MiTop.col0_alt f (sB b) (xB b)) FB
      (fun b => ((hZ n h₀ (sB b) (xB b)).1))
    rw [Fintype.sum_bool] at key
    have top : aB true * (f.t (sB true)).cTop (n + 1) * (f.t (sB true)).tail (2 * (n + 1)) h
          ((f.t (sB true)).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f (sB true) (xB true))) (FB true) +
        aB false * (f.t (sB false)).cTop (n + 1) * (f.t (sB false)).tail (2 * (n + 1)) h
          ((f.t (sB false)).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f (sB false) (xB false))) (FB false) = 0 := by
      have e1 := hcomm t (S.symm φ) G
      rw [LinearEquiv.apply_symm_apply] at e1
      have e2 := hTail (n + 1) hN t φ F F' hFF G hG1
      change α / (f.t W.P.A3.A.μ0).cBot * (f.t W.P.A3.A.μ0).cTop (n + 1) * (f.t W.P.A3.A.μ0).tail (2 * (n + 1)) hN
          ((f.t W.P.A3.A.μ0).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f W.P.A3.A.μ0 (S.symm φ₀))) G₀ +
        α' / (f.t t).cBot * (f.t t).cTop (n + 1) * (f.t t).tail (2 * (n + 1)) hN ((f.t t).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f t (S.symm φ))) G = 0
      rw [e1, e2]
      beta_reduce at hrel
      linear_combination hrel
    have bot := key top y v
    rw [Fintype.sum_bool] at bot
    have z1 := (hZ n h₀ W.P.A3.A.μ0 (S.symm φ₀)).2
      ((f.t W.P.A3.A.μ0).dn (2 * n + 1) ((f.t W.P.A3.A.μ0).ioT (2 * n) h G₀)) y v
    have z2 := (hZ n h₀ t (S.symm φ)).2 ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)) y v
    change α / (f.t W.P.A3.A.μ0).cBot * (f.t W.P.A3.A.μ0).cBot * (f.t W.P.A3.A.μ0).per 0 n h₀ (_root_.GlobalTheory.MiTop.col0_alt f W.P.A3.A.μ0 (S.symm φ₀))
        ((f.t W.P.A3.A.μ0).dn (2 * n + 1) ((f.t W.P.A3.A.μ0).ioT (2 * n) h G₀)) y v +
      α' / (f.t t).cBot * (f.t t).cBot * (f.t t).per 0 n h₀ (_root_.GlobalTheory.MiTop.col0_alt f t (S.symm φ))
        ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)) y v = 0 at bot
    rw [z1, z2] at bot
    have d1 : ((f.t W.P.A3.A.μ0).dn (2 * n + 1) ((f.t W.P.A3.A.μ0).ioT (2 * n) h G₀)).1 = T := hG₀
    have d2 : ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)).1 = _root_.GlobalTheory.MiTop.rowFormOfTuple W t F' := hGd
    rw [d1, d2, div_mul_cancel₀ _ (hBot _), div_mul_cancel₀ _ (hBot _)] at bot
    simpa only [LinearEquiv.coe_coe] using bot
end GlobalTheory.MiTop
end
end
