import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.PairLiftH
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftGeneralLinear
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Laws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepsum
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecLawsH

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.LocLanglands GlobalTheory.LocGL
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.SplitPairLift
namespace UpperTheory.One.M
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem pairLift_of_howeDuality_bernstein_alt : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.BernsteinUnitaryProductIrreducible → ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A) (S : Reading T), _root_.GlobalTheory.SplitRead.LawsAlt S → RowUnit S → PairRead S → RepGood S → ∀ i, PairLift N A i := by
  intro hBZ hB R H what₂ N A T S hL hU hP hG i σ P hpair w hw
  have hne : what₂.isot (N.j i) σ ≠ ⊥ := by
    obtain ⟨f, hf, F, -, hF⟩ := hpair
    intro hb
    rw [hb, Submodule.mem_bot] at hf
    apply hF
    rw [hf, map_zero, inner_zero_right]
  have hrt : R.r < R.t := by
    have := R.rank_add_five_le
    unfold Ranks.r
    omega
  have L := hL i w hw
  set X := S i w hw with hX
  let π' := twistIrr (X.rep P) X.eta_ok.1
  let cμ := detIrr 1 X.mu_ok.1
  let τ := detIrr R.t X.mu_ok.1
  let cη := detIrr 1 X.eta_ok.1.inv
  have h1 : Nonempty (π'.π.Equiv (prod₂ (X.row σ).π τ.π)) :=
    _root_.GlobalTheory.T.theta_lift_general_linear hBZ hB _ R.r R.t X.mu _ _ (X.row σ).π π'.π hrt X.mu_ok.1 X.mu_ok.2 (X.row σ).smooth
      (X.row σ).irr (hU i w hw σ hne) π'.smooth π'.irr (hP i w hw σ P hpair)
  have h2 := L.prod _ _ (X.row σ) τ π' h1
  have h3 := L.det R.t X.mu cμ τ ⟨.refl _⟩ ⟨.refl _⟩
  have hgπ : GoodI π' := by
    have e : cls (⟨π'.V, π'.π, π'.smooth, π'.irr⟩ : IrrRep (GL (Fin (R.r + R.t)) (w.adicCompletion H.E))) = (cls (⟨(X.rep P).V, (X.rep P).π, (X.rep P).smooth, (X.rep P).irr⟩ : IrrRep (GL (Fin (R.r + R.t)) (w.adicCompletion H.E)))).tw X.eta X.eta_ok.1 :=
      (IrrGL.tw_of (X.rep P).π (X.rep P).smooth (X.rep P).irr X.eta X.eta_ok.1).symm
    show UpperTheory.Zero.LLC.Good _
    rw [e]
    exact (GlobalTheory.RecT.good_tw_iff _ _ _).2 (hG i w hw P)
  have h4 := _root_.UpperTheory.One.M.RecLawsH.twist L _ X.eta⁻¹ cη π' (X.rep P) hgπ ⟨.refl _⟩ (by
    show Nonempty ((X.rep P).π.Equiv (twist (twist (X.rep P).π (detChar _ X.eta)) (detChar _ X.eta⁻¹)))
    rw [twist_twist_inv]
    exact ⟨.refl _⟩)
  have h5 := X.locMu cμ ⟨.refl _⟩
  have h6 := X.locEta cη ⟨.refl _⟩
  have h7 : A.lpDim (A.locG A.etaTinv w) = 1 := by
    rw [← T.dim, h6, L.dim]
  apply (T.e w).injective
  unfold liftPar
  rw [T.char _ _ _ h7, T.sum, e_spehLoc, X.locV, X.locW σ hne, h4, h2, h3, h6]
  show _ = ((X.rc _ (X.row σ)).lpSum (speh (T.e w (A.locG (A.muC i) w)) R.t)).lpChar _
  rw [h5]
end UpperTheory.One.M
end
end
