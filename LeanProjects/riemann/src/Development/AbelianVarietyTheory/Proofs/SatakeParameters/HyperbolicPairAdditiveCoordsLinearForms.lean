import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.KappaIntegralOfCalculation
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OfClosedInt
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.OrbEmb
import Formalism.GaussJetBounds.GaussJetProofs.OrbMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.JetTdegEqDegree
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesBConditionsLargePrime
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)
noncomputable section

namespace GlobalTheory.KerStd.HypOrbit

open Formalism.InvariantFactorPaths.G7 (lgF at1)

theorem lg_flin {p : ℕ} [Fact p.Prime] (hl : 2 ≤ p) {τ m : Type} [Fintype m] (c : m → ℂ_[p]) (v : m → MvPowerSeries τ ℂ_[p])
    (hv : ∀ k, constantCoeff (v k) = 0) :
    PowerSeries.subst (Formalism.L2.Th1.C.flin (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) c v) (lgF ℂ_[p] p) =
      ∑ k, C (c k) * PowerSeries.subst (v k) (lgF ℂ_[p] p) := by
  unfold Formalism.L2.Th1.C.flin
  have hA : constantCoeff (∑ k, C (c k) * PowerSeries.subst (v k) (lgF ℂ_[p] p)) = 0 := by
    simp only [map_sum, map_mul, constantCoeff_C]
    exact Finset.sum_eq_zero fun k _ => by
      rw [PowerSeries.constantCoeff_subst_eq_zero (hv k) _ (Formalism.L2.Th1.D.Pair.cc_lgF hl), mul_zero]
  rw [← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (Formalism.L2.Th1.D.expSpec ℂ_[p] p hl).1)
    (PowerSeries.HasSubst.of_constantCoeff_zero hA), (Formalism.L2.Th1.D.expSpec ℂ_[p] p hl).2.1,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hA)]

theorem cc_flin {p : ℕ} [Fact p.Prime] (hl : 2 ≤ p) {τ m : Type} [Fintype m] (c : m → ℂ_[p]) (v : m → MvPowerSeries τ ℂ_[p])
    (hv : ∀ k, constantCoeff (v k) = 0) :
    constantCoeff (Formalism.L2.Th1.C.flin (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) c v) = 0 := by
  unfold Formalism.L2.Th1.C.flin
  have hA : constantCoeff (∑ k, C (c k) * PowerSeries.subst (v k) (lgF ℂ_[p] p)) = 0 := by
    simp only [map_sum, map_mul, constantCoeff_C]
    exact Finset.sum_eq_zero fun k _ => by
      rw [PowerSeries.constantCoeff_subst_eq_zero (hv k) _ (Formalism.L2.Th1.D.Pair.cc_lgF hl), mul_zero]
  exact PowerSeries.constantCoeff_subst_eq_zero hA _ (Formalism.L2.Th1.D.expSpec ℂ_[p] p hl).1

theorem hypZ_of_inHyp : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {M N N' r : ℕ} (eA : Fin M ≃ R × Fin N)
    (f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p) (Θ : MvPowerSeries (Fin r) ℂ_[p]), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (Formalism.L2.Th1.D.thetaInZ (d := nP D p) p (MaximalUnramifiedExtension p).subtype σ om oms
        (subst (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' =>
            (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) :
              MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p]))
          (Formalism.L2.Th1.Top.inHyp p f f'
            (subst (fun i : Fin r => (Formalism.InvariantFactorPaths.G7.at1 i (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) Θ)))) =
      subst (hypZ D p σ om oms R f f') Θ := by
  intro D p _ hp σ om oms R M N N' r eA f f' Θ
  have hl : 2 ≤ p := by omega
  have hcl : PowerSeries.constantCoeff (lgF ℂ_[p] p) = 0 := Formalism.L2.Th1.D.Pair.cc_lgF hl
  have hA0 : HasSubst (fun i : Fin r => (at1 i (lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun i => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i hcl
  have hu : ∀ k : ((R × Fin (nP D p / 2)) × Fin N × Fin N') ⊕ ((R × Fin (nP D p / 2)) × Fin N × Fin N'),
      constantCoeff ((Sum.elim (fun e => (X (false, e) : MvPowerSeries (Bool × ((R × Fin (nP D p / 2)) × Fin N × Fin N')) ℂ_[p]))
        (fun e => X (true, e))) k) = 0 := by
    intro k; cases k <;> simp
  have hhc : HasSubst (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) (MaximalUnramifiedExtension p).subtype f f') :=
    hasSubst_of_constantCoeff_zero fun i => cc_flin hl _ _ hu

  have hL : ∀ i : Fin r, subst (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) (MaximalUnramifiedExtension p).subtype f f')
      (at1 i (lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p]) =
      ∑ e : (R × Fin (nP D p / 2)) × Fin N × Fin N',
        (C ((f e i : MaximalUnramifiedExtension p) : ℂ_[p]) * at1 (false, e) (lgF ℂ_[p] p) +
          C ((f' e i : MaximalUnramifiedExtension p) : ℂ_[p]) * at1 (true, e) (lgF ℂ_[p] p)) := by
    intro i
    rw [Formalism.L2.Th1.D.Pair.subst_single_var hhc]
    unfold Formalism.L2.Th1.E.hypCoord
    rw [lg_flin hl _ _ hu, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    rfl

  set ren1 := (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' =>
            (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) :
              MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p])) with hren1
  set Y := (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) with hYdef
  have hR : HasSubst ren1 := hasSubst_of_constantCoeff_zero fun x => constantCoeff_X _
  have hX : HasSubst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) :=
    hasSubst_of_constantCoeff_zero (CofactorConverse.cc_xOfZ hl _ σ om oms)
  have hY : HasSubst Y := hasSubst_of_constantCoeff_zero fun y => constantCoeff_X _
  have hRX0 : ∀ x, constantCoeff (subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) (ren1 x)) = 0 :=
    fun x => constantCoeff_subst_eq_zero hX (CofactorConverse.cc_xOfZ hl _ σ om oms) (constantCoeff_X _)
  have hRX : HasSubst (fun x => subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) (ren1 x)) :=
    hasSubst_of_constantCoeff_zero hRX0
  set W := (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' => subst Y
    (subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) (ren1 x))) with hWdef
  have hW : HasSubst W := hasSubst_of_constantCoeff_zero fun x =>
    constantCoeff_subst_eq_zero hY (fun y => constantCoeff_X _) (hRX0 x)
  have hcomp : ∀ g : MvPowerSeries (Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N') ℂ_[p], subst Y (subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms)
      (subst ren1 g)) = subst W g := by
    intro g
    rw [subst_comp_subst_apply hR hX, subst_comp_subst_apply hRX hY]
  have hLf : HasSubst (fun i : Fin r => subst (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) (MaximalUnramifiedExtension p).subtype f f')
      (at1 i (lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun i => constantCoeff_subst_eq_zero hhc (fun i => cc_flin hl _ _ hu)
      (Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i hcl)

  have hWx : ∀ (c : Bool) (e : (R × Fin (nP D p / 2)) × Fin N × Fin N'), subst W (at1 (c, e) (lgF ℂ_[p] p)) =
      ∑ s : ZMod (nP D p), C ((MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY σ om oms (c, e.1.2) s)) *
        (X (OrbitPlaces.orbMap D p e.1.1 s, e.2.1, e.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) := by
    intro c e
    rw [Formalism.L2.Th1.D.Pair.subst_single_var hW]
    simp only [hWdef, hren1]
    rw [subst_X hX]
    have ha : PowerSeries.HasSubst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms
        (c, e.1.2, eA.symm (e.1.1, e.2.1), e.2.2)) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (CofactorConverse.cc_xOfZ hl _ σ om oms _)
    rw [← Formalism.L2.Th1.D.Pair.subst_subst1 hY ha]
    have hlog := CofactorConverse.log_xOfZ (d := nP D p) hl (MaximalUnramifiedExtension p).subtype σ om oms (eA.symm (e.1.1, e.2.1)) e.2.2 (c, e.1.2)
    simp only at hlog
    rw [hlog]
    unfold CofactorConverse.linP
    rw [← coe_substAlgHom hY]
    simp only [map_sum, map_mul]
    simp only [coe_substAlgHom hY, subst_C]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [subst_X hY]
    simp only [hYdef, Equiv.apply_symm_apply]
  have hEv : ∀ (k : Fin (nP D p / 2)) (q : OrbitPlaces.Pl D) (a : Fin N) (b : Fin N'),
      (∑ s : ZMod (nP D p), C ((MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY σ om oms (false, k) s)) *
        (X (OrbitPlaces.orbMap D p q s, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) =
      linEv D p σ (oms k) q a b := by
    intro k q a b
    unfold linEv
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY
    by_cases hs : s.val % 2 = 0 <;> simp [hs]
  have hOd : ∀ (k : Fin (nP D p / 2)) (q : OrbitPlaces.Pl D) (a : Fin N) (b : Fin N'),
      (∑ s : ZMod (nP D p), C ((MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY σ om oms (true, k) s)) *
        (X (OrbitPlaces.orbMap D p q s, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) =
      linOd D p σ (om k) q a b := by
    intro k q a b
    unfold linOd
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY
    by_cases hs : s.val % 2 = 0 <;> simp [hs]
  unfold Formalism.L2.Th1.D.thetaInZ Formalism.L2.Th1.Top.inHyp
  rw [hcomp, subst_comp_subst_apply hA0 hhc, subst_comp_subst_apply hLf hW]
  congr 1
  funext i
  rw [hL i]

  rw [← coe_substAlgHom hW]
  simp only [map_sum, map_add, map_mul]
  simp only [coe_substAlgHom hW, subst_C, hWx, hEv, hOd]
  rfl

end GlobalTheory.KerStd.HypOrbit
