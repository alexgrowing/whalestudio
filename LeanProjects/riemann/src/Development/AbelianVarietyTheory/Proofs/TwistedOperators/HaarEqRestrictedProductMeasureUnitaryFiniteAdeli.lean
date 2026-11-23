import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionFiniteAdelicPureTensorEqLocalConvolut
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section
namespace GlobalTheory.FinMeasEq

variable {D : D7}

theorem locallyCompactSpace_GfC (V : HSp D) : LocallyCompactSpace (GfC V) :=
  locallyCompactSpace_finPts D.sp.cm.sig V.gram

theorem tensorFin_unitLoc (V : HSp D) (g : GFin D.sp.cm.sig V.gram) :
    tensorFin D.sp.cm.sig V.gram (unitLoc D.sp.cm.sig V.gram (frameLat V)) g =
      (levelOffFin D.sp.cm.sig V.gram (frameLat V) ∅ : Set (GFin D.sp.cm.sig V.gram)).indicator 1 g := by
  by_cases hg : g ∈ levelOffFin D.sp.cm.sig V.gram (frameLat V) ∅
  · rw [Set.indicator_of_mem hg]
    have hv := (mem_levelOffFin.1 hg).2
    unfold tensorFin
    rw [Pi.one_apply]
    refine (finprod_congr fun v => ?_).trans finprod_one
    simp [unitLoc, hv v (Finset.notMem_empty v)]
  · rw [Set.indicator_of_notMem hg]
    by_contra hne
    refine hg (mem_levelOffFin.2 ⟨fun v hv => absurd hv (Finset.notMem_empty v), fun v _ => ?_⟩)
    have := (isFinFamily_unit.tensorFin_ne_zero_iff g).1 hne v
    by_contra hv
    exact this (by simp [unitLoc, hv])

theorem finMeas_eq : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
    (νF : Measure (GFin D.sp.cm.sig V.gram)), IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF →
    ∀ (ν : Measure (GfC V)), IsFinMeas V μf ν → ∀ s : Set (GfC V), IsCompact (closure s) →
      ν s = νF ((finPtsEquiv D.sp.cm.sig V.gram) ⁻¹' s) := by
  intro D V μf νF hF ν hν s hs
  haveI := locallyCompactSpace_GfC V
  haveI : ν.IsHaarMeasure := hν.1
  set e := finPtsEquiv D.sp.cm.sig V.gram
  set ν' : Measure (GfC V) := νF.map e with hν'
  have hmap : ∀ t : Set (GfC V), ν' t = νF (e ⁻¹' t) := fun t =>
    e.toHomeomorph.toMeasurableEquiv.map_apply t
  haveI : ν'.IsHaarMeasure := (isRestrictedProdFinPts_iff.1 hF.map_finPts).2.1

  set Kf : Set (GFin D.sp.cm.sig V.gram) := (levelOffFin D.sp.cm.sig V.gram (frameLat V) ∅ : Set (GFin D.sp.cm.sig V.gram))
  set K : Set (GfC V) := e.symm ⁻¹' Kf with hK
  have hKo : IsOpen K := (isOpen_levelOffFin_empty _ _ _).preimage e.symm.continuous
  have hKf_closed : IsClosed Kf :=
    Subgroup.isClosed_of_isOpen _ (isOpen_levelOffFin_empty _ _ _)
  have hKc : IsClosed K := hKf_closed.preimage e.symm.continuous
  have hKcpt : IsCompact K := by
    have : K = e '' Kf := (e.toHomeomorph.image_eq_preimage_symm Kf).symm
    rw [this]
    exact (isCompact_levelOffFin _ _ _ ∅).image e.continuous
  have hKne : K.Nonempty := ⟨1, by
    change e.symm 1 ∈ Kf
    rw [map_one]
    exact Subgroup.one_mem _⟩

  have h1 : ν' K = ∏ᶠ v, μf v (stabLoc D.sp.cm.sig V.gram (frameLat V) v) := by
    rw [hmap]
    refine (congrArg νF (Set.ext fun x => ?_)).trans hF.measure_level
    change e.symm (e x) ∈ Kf ↔ _
    rw [e.symm_apply_apply]
  have hfin : (Function.mulSupport fun v => μf v (stabLoc D.sp.cm.sig V.gram (frameLat V) v)).Finite :=
    Filter.eventually_cofinite.1 (isRestrictedProdFin_iff.1 hF).2.2.1
  have h2 : ν.real K = ∏ᶠ v, (μf v).real (stabLoc D.sp.cm.sig V.gram (frameLat V) v) := by
    have hi := hν.2 _ isFinFamily_unit
    have hfn : finFn V (unitLoc D.sp.cm.sig V.gram (frameLat V)) = K.indicator (fun _ => (1 : ℂ)) := by
      funext y
      rw [GlobalTheory.TrConv.finFn_eq_tensorFin, tensorFin_unitLoc]
      rfl
    rw [hfn, integral_indicator_const _ hKo.measurableSet] at hi
    have hloc : ∀ v, ∫ x, unitLoc D.sp.cm.sig V.gram (frameLat V) v x ∂μf v =
        (((μf v).real (stabLoc D.sp.cm.sig V.gram (frameLat V) v) : ℝ) : ℂ) := fun v => by
      have := (isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v).measurableSet
      rw [unitLoc, show (1 : GLoc D.sp.cm.sig V.gram v → ℂ) = fun _ => 1 from rfl,
        integral_indicator_const _ this]
      simp
    simp_rw [hloc] at hi
    have hc : (∏ᶠ v, (((μf v).real (stabLoc D.sp.cm.sig V.gram (frameLat V) v) : ℝ) : ℂ)) =
        ((∏ᶠ v, (μf v).real (stabLoc D.sp.cm.sig V.gram (frameLat V) v) : ℝ) : ℂ) :=
      (Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective _).symm
    rw [Complex.real_smul, mul_one, hc] at hi
    exact_mod_cast hi
  have h3 : ν K = ν' K := by
    rw [h1]
    have hK' : ν K ≠ ⊤ := hKcpt.measure_lt_top.ne
    have hP : ∏ᶠ v, μf v (stabLoc D.sp.cm.sig V.gram (frameLat V) v) ≠ ⊤ := by
      rw [← h1]; exact hKcpt.measure_lt_top.ne
    rw [← ENNReal.toReal_eq_toReal_iff' hK' hP]
    rw [show (ν K).toReal = ν.real K from rfl, h2]
    exact (ENNReal.toRealHom.map_finprod hfin).symm
  have hc := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure ν ν' (s := K)
    (by rw [hKc.closure_eq]; exact hKcpt)
  have hc1 : Measure.haarScalarFactor ν ν' = 1 := by
    have hpos : ν' K ≠ 0 := hKo.measure_ne_zero ν' hKne
    have htop : ν' K ≠ ⊤ := hKcpt.measure_lt_top.ne
    rw [h3, ENNReal.smul_def, smul_eq_mul] at hc
    have := (ENNReal.mul_left_inj hpos htop).1 ((one_mul _).trans hc)
    exact_mod_cast this.symm
  rw [Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure ν ν' hs, hc1, one_smul, hmap]

end GlobalTheory.FinMeasEq
