import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicPairAdditiveCoordsLinearFormsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExpFactorAllOrbitsEqProdOrbitsStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd
namespace IntegralSeriesSubstitution
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)

theorem orb_bijective (D : D7) (p : ℕ) (R : Finset (OrbitPlaces.Pl D)) (hR : OrbitPlaces.IsReps D p R) :
    Function.Bijective (fun x : R × ZMod (nP D p) => OrbitPlaces.orbMap D p x.1 x.2) := by
  constructor
  · rintro ⟨⟨r, hr⟩, s⟩ ⟨⟨r', hr'⟩, s'⟩ h
    simp only at h
    have h1 : ∃ e : ℕ, posPl D p r e = OrbitPlaces.orbMap D p r s := ⟨s.val, rfl⟩
    have h2 : ∃ e : ℕ, posPl D p r' e = OrbitPlaces.orbMap D p r s := ⟨s'.val, h.symm⟩
    obtain ⟨r0, -, huniq⟩ := hR (OrbitPlaces.orbMap D p r s)
    have hrr : r = r' := (huniq r ⟨hr, h1⟩).trans (huniq r' ⟨hr', h2⟩).symm
    subst hrr
    have hs : s = s' := PI.OrbJet.OrbW.orbMap_inj D p r h
    subst hs
    rfl
  · intro z
    obtain ⟨r, ⟨hr, e, he⟩, -⟩ := hR z
    refine ⟨(⟨r, hr⟩, (e : ZMod (nP D p))), ?_⟩
    show OrbitPlaces.orbMap D p r (e : ZMod (nP D p)) = z
    exact (PI.OrbJet.OrbW.posPl_eq_orbMap D p r e).symm.trans he

theorem subst_entLog_orb (D : D7) (p : ℕ) [Fact p.Prime] {M N N' : ℕ} (κ : Fin M → OrbitPlaces.Pl D × Fin N)
    (y : ZV (nP D p) M N') :
    subst (fun y' : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (κ y'.2.1).1 y'.1, (κ y'.2.1).2, y'.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (entLog (K := ℂ_[p]) p y) = OrbitPlaces.logPl D p (OrbitPlaces.orbMap D p (κ y.2.1).1 y.1, (κ y.2.1).2, y.2.2) := by
  obtain ⟨s, a', b⟩ := y
  have hY : HasSubst (fun s' : ZMod (nP D p) => (X (s', a', b) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hπ : HasSubst (fun y' : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (κ y'.2.1).1 y'.1, (κ y'.2.1).2, y'.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hY2 : HasSubst (fun s' : ZMod (nP D p) => (X (s', (κ a').2, b) : MvPowerSeries (ZV (nP D p) N N') ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hP : HasSubst (X ∘ ⇑(PI.OrbJet.AU.pE D p (κ a').1 (Fin N × Fin N')) :
      ZMod (nP D p) × Fin N × Fin N' → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hE := PI.OrbJet.AU.rename_jet D p (β := Fin N × Fin N') (κ a').1 (s, (κ a').2, b)
  rw [Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel.jetLogG_eq_entLog p (nP D p) N N' (s, (κ a').2, b),
    GlobalTheory.KerStd.CofactorConverse.entLog_eq_letLog, MvPowerSeries.rename_eq_subst,
    subst_comp_subst_apply hY2 hP] at hE
  show _ = PI.OrbJet.logPl D p (PI.OrbJet.AU.pE D p (κ a').1 (Fin N × Fin N') (s, (κ a').2, b))
  rw [← hE, GlobalTheory.KerStd.CofactorConverse.entLog_eq_letLog, subst_comp_subst_apply hY hπ]
  congr 1
  funext s'
  rw [subst_X hπ, subst_X hP]
  rfl

theorem integral_subst_X_of_injective {K : Type} [NormedField K] {σ τ : Type} [Finite σ] (φ : σ → τ)
    (hφ : Function.Injective φ) {U : MvPowerSeries σ K} (hU : Integral U) :
    Integral (subst (fun x => (X (φ x) : MvPowerSeries τ K)) U) := by
  classical
  let e : σ ↪ τ := ⟨φ, hφ⟩
  have h : subst (fun x => (X (φ x) : MvPowerSeries τ K)) U = rename e U := by
    rw [rename_eq_subst]; rfl
  intro n
  rw [h]
  by_cases hn : ∃ m, Finsupp.embDomain e m = n
  · obtain ⟨m, rfl⟩ := hn
    rw [coeff_embDomain_rename]
    exact hU m
  · rw [coeff_rename_eq_zero]
    · simp
    · rintro ⟨m, hm⟩
      exact hn ⟨m, by rw [Finsupp.embDomain_eq_mapDomain]; exact hm⟩

theorem sumE_reindex {K : Type} [Field K] {R ι : Type} [Fintype R] [Fintype ι] {M N N' : ℕ} (eA : Fin M ≃ R × Fin N)
    (be : MvPowerSeries (Fin 2) K) :
    subst (fun x : Bool × (R × ι) × Fin N × Fin N' =>
        (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) : MvPowerSeries (Bool × ι × Fin M × Fin N') K))
      (Formalism.L2.Th1.D.sumE (ι := R × ι) (N0 := N) (N1 := N') be) = Formalism.L2.Th1.D.sumE (ι := ι) (N0 := M) (N1 := N') be := by
  have hρ : HasSubst (fun x : Bool × (R × ι) × Fin N × Fin N' =>
      (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) : MvPowerSeries (Bool × ι × Fin M × Fin N') K)) :=
    hasSubst_of_constantCoeff_zero fun x => constantCoeff_X _
  unfold Formalism.L2.Th1.D.sumE
  rw [← coe_substAlgHom hρ, map_sum]
  let E : (R × ι) × Fin N × Fin N' ≃ ι × Fin M × Fin N' :=
    { toFun := fun e => (e.1.2, eA.symm (e.1.1, e.2.1), e.2.2)
      invFun := fun e => (((eA e.2.1).1, e.1), (eA e.2.1).2, e.2.2)
      left_inv := fun ⟨⟨r, k⟩, a, b⟩ => by simp
      right_inv := fun ⟨k, a, b⟩ => by simp }
  refine Fintype.sum_equiv E _ _ fun e => ?_
  rw [coe_substAlgHom, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun a => constantCoeff_X _) hρ]
  congr 1
  funext a
  rw [subst_X hρ]
  split_ifs <;> rfl

theorem orbitIdentity_all_of_integralClass_hostLog : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → OrbitPlaces.OrbOK D p → ∀ (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (ζ : MaximalUnramifiedExtension p), BeData p (nP D p) σ F (cob F (phFF p g2 g3 s2 ε)) om oms ζ → ∀ (R : Finset (OrbitPlaces.Pl D)), OrbitPlaces.IsReps D p R → ∀ (N N' r : ℕ) (f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p), HypPair σ f f' → ∀ (Θ : MvPowerSeries (Fin r) ℂ_[p]), HostLog p g2 g3 s2 ε Θ → ∀ (ep : ℂ_[p]) (Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (hypZ D p σ om oms R f f') Θ → OrbitPlaces.ThetaExpansionAllPlaces D p R ep (fun _ => -1) (fun _ => beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ) Th := by
  intro D p _ g2 g3 s2 ε σ F hC hO om oms ζ hB R hR N N' r f f' hH Θ hΘ ep Th hTh
  obtain ⟨h5, hg2, hg3, hε, hth, hσ, hF, hN⟩ := hC
  have hBd := hB
  obtain ⟨-, -, hF1, hF2, hOw, hTr, hζ⟩ := hB
  have hI := (HostLog.iff_phSum p g2 g3 s2 ε Θ).1 hΘ
  obtain ⟨U0, Φ, hU0, hΦ0, hsim, hEq⟩ := Formalism.L2.Th1.Top.HypShape_of Formalism.L2.Th1.Top.CalcC_proof p h5 g2 g3 ε s2
    hg2 hg3 hε hth σ hσ F hF hN N N' (R × Fin (nP D p / 2)) (Fin r) f f' hH _ hI

  let M := Fintype.card R * N
  let eA : Fin M ≃ R × Fin N :=
    finProdFinEquiv.symm.trans ((Fintype.equivFin R).symm.prodCongr (Equiv.refl _))
  let rv : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' → Bool × Fin (nP D p / 2) × Fin M × Fin N' :=
    fun x => (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2)
  have hrv : Function.Injective rv := by
    rintro ⟨c, ⟨a1, k⟩, a2, b⟩ ⟨c', ⟨a1', k'⟩, a2', b'⟩ h
    simp only [rv, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have h3' := congrArg eA h3
    simp only [Equiv.apply_symm_apply, Prod.mk.injEq] at h3'
    rw [h1, h2, h3'.1, h3'.2, h4]
  let ρs : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' → MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p] :=
    fun x => X (rv x)
  have hρs : HasSubst ρs := hasSubst_of_constantCoeff_zero fun x => constantCoeff_X _
  have hU0' : Integral (subst ρs U0) := integral_subst_X_of_injective rv hrv hU0
  have hΦ0' : constantCoeff (subst ρs Φ) = 0 :=
    constantCoeff_subst_eq_zero hρs (fun x => constantCoeff_X _) hΦ0
  have hsE := sumE_reindex (ι := Fin (nP D p / 2)) (N' := N') eA (map (MaximalUnramifiedExtension p).subtype (cob F (phFF p g2 g3 s2 ε)))
  have hρe : ρs = fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' =>
      (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) : MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p]) := rfl
  rw [← hρe] at hsE
  have hsim' : Formalism.InvariantFactorPaths.G7.Simeq (subst ρs Φ)
      (Formalism.L2.Th1.D.sumE (ι := Fin (nP D p / 2)) (N0 := M) (N1 := N') (map (MaximalUnramifiedExtension p).subtype (cob F (phFF p g2 g3 s2 ε)))) := by
    rw [← hsE]
    refine ⟨?_, ?_⟩
    · rw [← subst_sub hρs]
      exact constantCoeff_subst_eq_zero hρs (fun x => constantCoeff_X _) hsim.1
    · rw [← subst_sub hρs, ← Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hρs hsim.1]
      exact integral_subst_X_of_injective rv hrv hsim.2
  obtain ⟨U, hU, hUeq⟩ := Formalism.L2.Th1.D.b0 (MaximalUnramifiedExtension p) ℂ_[p] p (nP D p) M N' σ (MaximalUnramifiedExtension p).subtype hσ (fun a => rfl)
    hO.two hO.even F hF _ hF1 hF2 (Fin (nP D p / 2)) om oms hOw hTr ζ hζ (subst ρs U0) (subst ρs Φ) hU0' hΦ0' hsim'

  obtain ⟨g, hg0, hg1, hg2⟩ := Formalism.DworkPowerSeriesWeights.generalized_log_inverse.{0, 0} ℂ_[p] p (Fact.out)
    (ZV (nP D p) M N') (fun y => (y.1 - 2, y.2.1, y.2.2))
  have hent := (Formalism.DworkPowerSeriesWeights.logarithm_weight_comparison.{0} ℂ_[p] p (nP D p) M N').2.1
  have hgE : ∀ y, subst g (entLog (K := ℂ_[p]) p y) = X y := fun y => by rw [hent]; exact hg1 y
  have hfun : entLog (K := ℂ_[p]) (d := nP D p) (N0 := M) (N1 := N') p =
      Formalism.DworkPowerSeriesWeights.genLog p (fun y : ZV (nP D p) M N' => (y.1 - 2, y.2.1, y.2.2)) := funext hent
  have hEg : ∀ y, subst (entLog (K := ℂ_[p]) (d := nP D p) (N0 := M) (N1 := N') p) (g y) = X y := fun y => by
    rw [hfun]; exact hg2 y
  have hZ := hUeq g hg0 hgE
  have hR1 : mvExp (-subst ρs Φ) * subst ρs U0 = subst ρs (Formalism.L2.Th1.Top.inHyp p f f'
      (subst (fun i : Fin r => (Formalism.InvariantFactorPaths.G7.at1 i (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) Θ)) := by
    rw [hEq, subst_mul hρs, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hρs (by rw [map_neg, hΦ0, neg_zero]),
      Formalism.L2.Th1.D.BiextensionSums.subst_neg' hρs]

  let πv : ZV (nP D p) M N' → OrbitPlaces.Pl D × Fin N × Fin N' :=
    fun y => (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2)
  have hπv : Function.Injective πv := by
    rintro ⟨s, a, b⟩ ⟨s', a', b'⟩ h
    simp only [πv, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hb := (orb_bijective D p R hR).1 (a₁ := ((eA a).1, s)) (a₂ := ((eA a').1, s')) h1
    simp only [Prod.mk.injEq] at hb
    have ha : eA a = eA a' := Prod.ext hb.1 h2
    rw [hb.2, eA.injective ha, h3]
  let πs : ZV (nP D p) M N' → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] := fun y => X (πv y)
  have hπs : HasSubst πs := hasSubst_of_constantCoeff_zero fun x => constantCoeff_X _
  have hgs : HasSubst g := hasSubst_of_constantCoeff_zero hg0
  have hbe0 : constantCoeff (beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ) = 0 :=
    Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel.constant_coeff_zero_of_vanishing_alt p (nP D p) (GlobalTheory.KerStd.bHyps_of_beStd p (nP D p) _ h5 hO.two hO.even
      ⟨σ, F, _, om, oms, ζ, hBd, rfl⟩).2.2.1
  have hπe : πs = fun y : ZV (nP D p) M N' =>
      (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) := rfl
  have hc := GlobalTheory.T.orbitPlaces_thetaSeries_subst_orbMap_eq D p h5 σ om oms R eA f f' Θ
  rw [← hρe, ← hπe] at hc
  have hA := congrArg (subst πs) hZ
  rw [hR1, hc] at hA
  rw [Formalism.DworkPowerSeriesWeights.thetaZ, subst_mul hπs] at hA
  have hlin : subst (Formalism.DworkPowerSeriesWeights.linSub Formalism.DworkPowerSeriesWeights.idM) (subst g U) = subst g U := by
    have : (Formalism.DworkPowerSeriesWeights.linSub Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → MvPowerSeries (ZV (nP D p) M N') ℂ_[p]) = X :=
      funext fun x => Formalism.DworkPowerSeriesWeights.OrbMul.linSub_idM x
    rw [this, subst_self]; rfl
  rw [hlin, subst_comp_subst_apply hgs hπs] at hA
  have hexp := GlobalTheory.T.expFactor_allOrbits_eq_prod_orbits D p R (N' := N') eA (beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ) hbe0
  rw [← hπe] at hexp
  rw [show (MvPowerSeries.map (MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.beMean p σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ)) =
    beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ from rfl] at hA
  rw [hexp] at hA

  have hlog : HasSubst (OrbitPlaces.logPl D p (β := Fin N × Fin N')) :=
    hasSubst_of_constantCoeff_zero (PI.OrbJet.AU.cc_log D p)
  refine ⟨subst πs U, integral_subst_X_of_injective πv hπv hU, ?_⟩
  have hCX : HasSubst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
      (C ep * X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun v => by simp
  have h1 : subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => C ep * OrbitPlaces.logPl D p v) Th =
      subst (OrbitPlaces.logPl D p (β := Fin N × Fin N')) (subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
        (C ep * X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th) := by
    rw [subst_comp_subst_apply hCX hlog]
    congr 1
    funext v
    rw [subst_mul hlog, subst_C, subst_X hlog]
  rw [h1, hTh, hA, subst_mul hlog]
  congr 1
  have hπg : HasSubst (fun y => subst πs (g y)) :=
    hasSubst_of_constantCoeff_zero fun y => constantCoeff_subst_eq_zero hπs (fun x => constantCoeff_X _) (hg0 y)
  rw [subst_comp_subst_apply hπg hlog]
  congr 1
  funext y
  have hlgE : HasSubst (entLog (K := ℂ_[p]) (d := nP D p) (N0 := M) (N1 := N') p) := by
    exact hasSubst_of_constantCoeff_zero fun v => by
      rw [← Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel.jetLogG_eq_entLog]
      exact Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel.cc_jetLogG p (nP D p) v
  rw [subst_comp_subst_apply hπs hlog]
  have e : (fun y' => subst (OrbitPlaces.logPl D p (β := Fin N × Fin N')) (πs y')) =
      fun y' => subst πs (entLog (K := ℂ_[p]) p y') := by
    funext y'
    rw [subst_X hlog]
    exact (subst_entLog_orb D p (N' := N') (fun a => ((eA a).1, (eA a).2)) y').symm
  rw [e, ← subst_comp_subst_apply hlgE hπs, hEg, subst_X hπs]

end IntegralSeriesSubstitution
end GlobalTheory.KerStd
