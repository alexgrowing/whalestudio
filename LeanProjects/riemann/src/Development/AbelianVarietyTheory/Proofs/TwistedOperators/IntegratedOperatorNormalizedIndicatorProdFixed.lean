import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFamOfNotMem
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

theorem integralOp_normInd_fix : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ (K' : ∀ v, Subgroup (GLoc D.sp.cm.sig V.gram v)), (∀ v, IsOpen (K' v : Set (GLoc D.sp.cm.sig V.gram v))) → (∀ v, K' v ≤ Kv V v) → (∀ᶠ v in cofinite, K' v = Kv V v) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) (x : W), (∀ g : GfC V, (∀ v, finLoc V v g ∈ K' v) → σ g x = x) → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fun v => normInd (μf v) (K' v : Set (GLoc D.sp.cm.sig V.gram v)))) P → P x = x := by
  intro D V μf hH h1 ν hν K' hO hle hcof W _ _ σ x hx P hP
  set c : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ :=
    fun v => normInd (μf v) (K' v : Set (GLoc D.sp.cm.sig V.gram v)) with hc
  have hcpt : ∀ v, IsCompact (K' v : Set (GLoc D.sp.cm.sig V.gram v)) := fun v =>
    (isCompact_stabLoc _ _ (frameLat V) v).of_isClosed_subset ((K' v).isClosed_of_isOpen (hO v)) (hle v)
  have hpos : ∀ v, (μf v).real (K' v : Set (GLoc D.sp.cm.sig V.gram v)) ≠ 0 := fun v => by
    have := hH v
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨(hO v).measure_ne_zero (μf v) ⟨1, (K' v).one_mem⟩, (hcpt v).measure_lt_top.ne⟩
  have hint : ∀ v, ∫ y, c v y ∂μf v = 1 := fun v => by
    simp only [hc, normInd, Pi.smul_apply]
    rw [integral_smul]
    erw [integral_indicator_const (μ := μf v) (1 : ℂ) (hO v).measurableSet]
    simp only [Complex.real_smul, smul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 (hpos v))
  have hfam : IsFinFamily D.sp.cm.sig V.gram (frameLat V) c := by
    refine ⟨fun v => Submodule.smul_mem _ _ (indicator_mem_SB (hO v) (hcpt v)), ?_⟩
    filter_upwards [hcof, h1] with v hv hv1
    simp only [hc, normInd, unitLoc, hv]
    simp [Measure.real, hv1]
  have hI : ∫ g, finFn V c g ∂ν = 1 := by
    rw [hν.2 c hfam]
    simp [hint]
  have hsupp : ∀ g : GfC V, finFn V c g ≠ 0 → ∀ v, finLoc V v g ∈ K' v := by
    intro g hg v
    have hfin : (Function.mulSupport fun v => c v (proj D.sp.cm.sig V.gram v (g : GA D V))).Finite :=
      Filter.eventually_cofinite.1 ((hfam.2.and (eventually_proj_mem_stabLoc _ _ (frameLat V) (g : GA D V))).mono
        fun v hv => by show c v _ = 1; rw [hv.1, unitLoc, indicator_of_mem hv.2, Pi.one_apply])
    by_contra hv
    apply hg
    refine finprod_eq_zero _ v ?_ hfin
    change normInd (μf v) (K' v : Set (GLoc D.sp.cm.sig V.gram v)) (finLoc V v g) = 0
    simp [normInd, Set.indicator_of_notMem hv]
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  have e : (fun g => finFn V c g * l (σ g x)) = fun g => finFn V c g * l x := by
    funext g
    by_cases h : finFn V c g = 0
    · simp [h]
    · rw [hx g (hsupp g h)]
  rw [map_sub, (hP x l).2, e, integral_mul_const, hI, one_mul, sub_self]

end GlobalTheory.TrIdem
