import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseOfOfPin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LiftClassSum

theorem exists_low (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (j : Fin D.R.m) :
    ∃ u : ∀ ρ, lowT (X.R.MW j (sg0 D X.A3.A)) ρ, (fun ρ => (u ρ : ↥((X.R.MW j (sg0 D X.A3.A)).sm ρ))) = X.geo.v₀ j (sg0 D X.A3.A) := by
  have h := (Y.Z.vec j).1
  exact ⟨fun ρ => ⟨X.geo.v₀ j _ ρ, (h ρ).2.1⟩, rfl⟩

open Classical in

theorem sum_eq_classSum_ωP (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (t : X.T) (hxi : X.R.xi t = (Y.Z.ρ.B i j b).de.chi) (hQ : X.R.Q t = (Y.Z.ρ.B i j b).de.Q) :
    Y.Z.ρ.sum i j b 0 ∅ 1 = (Y.Z.ρ.B i j b).classSum (X.R.ωP j t) (Y.Z.ρ.tw i b 0 ∅ 1) (Y.Z.ρ.rep i j b (Y.Z.ρ.tw i b 0 ∅ 1)) := by
  have hB : GlobalTheory.ConjTwist.BaseOf X.R.toRealDat j (Y.Z.ρ.B i j b) :=
    GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have hG : (Y.Z.ρ.B i j b).Good := Y.Z.good.base i j b
  have htup : GlobalTheory.ConjTwist.IsTupOf X.R.toRealDat (Y.Z.ρ.B i j b) (Twist.triv Circle ∅) t := by
    classical
    exact
      ⟨by rw [hxi]; exact (mul_one _).symm, by rw [hQ]; exact (Finset.union_empty _).symm⟩
  have h1 : IsWeilDatumO X.R.toRealDat.ψ (Vc D j) (Wc D j) (Lift.chrTh (X.R.toRealDat.toLevCh.mu t) X.R.toRealDat.eta ((j : ℕ) + 1)).1
      (Lift.chrTh (X.R.toRealDat.toLevCh.mu t) X.R.toRealDat.eta ((j : ℕ) + 1)).2 (Y.Z.ρ.om i j b 1) := by
    have := Y.Z.good.weil_base i j b
    rw [Base.IsWeil, show (1 : (AE D)ˣ →* Circle) = (Twist.triv Circle ∅ : Twist D Circle).chi from rfl,
      hB.mu_mul htup, hB.ψ, hB.eta] at this
    exact this
  have hu := (GlobalTheory.SplitChange.change_of_splitting D X.R.toRealDat.ψ (Vc D j) (Wc D j) (X.R.toRealDat.toLevCh.mu t) X.R.toRealDat.eta (Y.Z.ρ.B i j b).mu0
    ((j : ℕ) + 1) (X.R.ωP j t) (X.char.thP.ωP j t) hG.hecke hG.real).2.2 _ h1
  have key : ∀ τ : Twist D Circle, τ.Q = ∅ → τ.chi = 1 → ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      series (Y.Z.ρ.B i j b).F (Y.Z.ρ.om i j b τ.chi) ((Y.Z.ρ.B i j b).vecFlat τ) h P =
        series (Y.Z.ρ.B i j b).F (X.R.ωP j t) ((Y.Z.ρ.B i j b).vecFlat τ) h P := by
    rintro ⟨Q0, c0, r0⟩ hq hc h P
    dsimp only at hq hc
    subst hq hc
    funext g
    rw [series_apply, series_apply]
    have ht := Base.isThetaFunO_fock_vecAt hG (Base.admissible_empty_of_good hG) (fun _ _ => (1 : ℂ)) P
    rw [hB.ψ] at ht
    exact congrFun (hu (h, g) _ ht) 0
  apply LinearMap.ext
  intro F
  rw [Setup.sum, Base.classSum_apply, Base.classSum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [key _ (half_empty _) (charOf_one _ _)]

end GlobalTheory.LiftClassSum

end
