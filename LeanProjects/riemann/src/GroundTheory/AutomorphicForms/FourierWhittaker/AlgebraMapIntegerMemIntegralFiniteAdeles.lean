import Mathlib
import GroundTheory.AutomorphicForms.FourierWhittaker.Series
import GroundTheory.GlobalFields.TateThesis.LatticePoisson
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain
  Module
open scoped NumberField.AdeleRing FourierTransform

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

variable (K) in

abbrev BIdx : Type _ := Free.ChooseBasisIndex ℤ (𝓞 K)

def ofCoord (t : BIdx K → ℝ) : InfiniteAdeleRing K :=
  GroundTheory.Global.mixedToInfinite K ((latticeBasis K).equivFun.symm t)

def coordOf (y : InfiniteAdeleRing K) : BIdx K → ℝ :=
  (latticeBasis K).equivFun (GroundTheory.Global.homeomorphMixedSpace K y)

theorem ofCoord_coordOf (y : InfiniteAdeleRing K) : ofCoord (coordOf y) = y := by
  rw [ofCoord, coordOf, LinearEquiv.symm_apply_apply,
    GroundTheory.Global.mixedToInfinite_homeomorphMixedSpace]

theorem coordOf_ofCoord (t : BIdx K → ℝ) : coordOf (ofCoord t) = t := by
  rw [coordOf, ofCoord, GroundTheory.Global.homeomorphMixedSpace_mixedToInfinite,
    LinearEquiv.apply_symm_apply]

theorem ofCoord_add (s t : BIdx K → ℝ) : ofCoord (s + t) = ofCoord s + ofCoord t := by
  simp [ofCoord, map_add]

theorem continuous_ofCoord : Continuous (ofCoord (K := K)) :=
  GroundTheory.Global.continuous_mixedToInfinite.comp (LinearMap.continuous_of_finiteDimensional _)

theorem continuous_coordOf : Continuous (coordOf (K := K)) :=
  (LinearMap.continuous_of_finiteDimensional _).comp (GroundTheory.Global.homeomorphMixedSpace K).continuous

theorem homeomorphMixedSpace_ofCoord (t : BIdx K → ℝ) :
    GroundTheory.Global.homeomorphMixedSpace K (ofCoord t) = ∑ j, t j • latticeBasis K j := by
  rw [ofCoord, GroundTheory.Global.homeomorphMixedSpace_mixedToInfinite, Basis.equivFun_symm_apply]

theorem homeomorphMixedSpace_algebraMap (q : K) :
    GroundTheory.Global.homeomorphMixedSpace K (algebraMap K (InfiniteAdeleRing K) q) = mixedEmbedding K q := by
  rw [← GroundTheory.Global.mixedToInfinite_mixedEmbedding, GroundTheory.Global.homeomorphMixedSpace_mixedToInfinite]

theorem ofCoord_intCast (n : BIdx K → ℤ) :
    ofCoord (fun j => (n j : ℝ)) =
      algebraMap K (InfiniteAdeleRing K) (algebraMap (𝓞 K) K (∑ j, n j • RingOfIntegers.basis K j)) := by
  apply (GroundTheory.Global.homeomorphMixedSpace K).injective
  rw [homeomorphMixedSpace_ofCoord, homeomorphMixedSpace_algebraMap, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [latticeBasis_apply, integralBasis_apply, map_zsmul, map_zsmul, Int.cast_smul_eq_zsmul]

theorem mem_fundamentalSetInfinite_iff (y : InfiniteAdeleRing K) :
    y ∈ GroundTheory.Global.fundamentalSetInfinite K ↔ ∀ j, coordOf y j ∈ Ico (0 : ℝ) 1 := by
  simp [GroundTheory.Global.fundamentalSetInfinite, coordOf, ZSpan.mem_fundamentalDomain]

theorem infiniteTrace_algebraMap_mul_ofCoord (q : K) (t : BIdx K → ℝ) :
    GroundTheory.Global.infiniteTrace K (algebraMap K (InfiniteAdeleRing K) q * ofCoord t) =
      ∑ j, t j * (Algebra.trace ℚ K (q * integralBasis K j) : ℝ) := by
  rw [← GroundTheory.Global.mixedTrace_homeomorphMixedSpace, GroundTheory.Global.homeomorphMixedSpace_mul,
    homeomorphMixedSpace_algebraMap, homeomorphMixedSpace_ofCoord, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, latticeBasis_apply, ← map_mul,
    GroundTheory.Global.mixedTrace_mixedEmbedding, smul_eq_mul]

variable (K) in

def traceDualBasis : Basis (BIdx K) ℚ K :=
  (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) (integralBasis K)

theorem trace_traceDualBasis_mul (i j : BIdx K) :
    Algebra.trace ℚ K (traceDualBasis K i * integralBasis K j) = if j = i then 1 else 0 := by
  rw [← Algebra.traceForm_apply, traceDualBasis, LinearMap.BilinForm.apply_dualBasis_left]

def dualVec (n : ι × BIdx K → ℤ) : ι → K := fun i => ∑ j, (n (i, j) : ℚ) • traceDualBasis K j

theorem trace_dualVec_mul (n : ι × BIdx K → ℤ) (i : ι) (k : BIdx K) :
    Algebra.trace ℚ K (dualVec n i * integralBasis K k) = n (i, k) := by
  classical
  simp only [dualVec, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul,
    trace_traceDualBasis_mul, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem dualVec_injective : Function.Injective (dualVec (K := K) (ι := ι)) := by
  intro n m h
  funext p
  have := trace_dualVec_mul n p.1 p.2
  rw [h, trace_dualVec_mul] at this
  exact_mod_cast this.symm

theorem isDual_dualVec (n : ι × BIdx K → ℤ) : IsDual (dualVec n) := by
  intro i
  rw [GroundTheory.Global.algebraMap_mem_finiteInvDifferent_iff]
  intro a
  have ha : algebraMap (𝓞 K) K a =
      ∑ k, ((RingOfIntegers.basis K).repr a k : ℚ) • integralBasis K k := by
    conv_lhs => rw [← (RingOfIntegers.basis K).sum_repr a]
    simp [map_sum, integralBasis_apply, Int.cast_smul_eq_zsmul]
  rw [ha, Finset.mul_sum, map_sum]
  refine sum_mem fun k _ => ?_
  rw [mul_smul_comm, map_smul, trace_dualVec_mul, smul_eq_mul]
  exact ⟨(RingOfIntegers.basis K).repr a k * n (i, k), by rw [map_mul, eq_intCast, eq_intCast]⟩

theorem exists_dualVec_eq {ξ : ι → K} (hξ : IsDual ξ) : ∃ n, dualVec n = ξ := by
  have hint : ∀ i k, ∃ m : ℤ, Algebra.trace ℚ K (ξ i * integralBasis K k) = m := by
    intro i k
    obtain ⟨m, hm⟩ := (GroundTheory.Global.algebraMap_mem_finiteInvDifferent_iff (ξ i)).1 (hξ i)
      (RingOfIntegers.basis K k)
    exact ⟨m, by rw [integralBasis_apply, ← hm]; rfl⟩
  choose m hm using hint
  refine ⟨fun p => m p.1 p.2, funext fun i => ?_⟩
  rw [dualVec]
  conv_rhs => rw [← (traceDualBasis K).sum_repr (ξ i)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [traceDualBasis, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, hm]

def torusPt (t : ι × BIdx K → ℝ) : ι → 𝔸[K] :=
  fun i => GroundTheory.Global.infiniteAdeleInl (ofCoord fun j => t (i, j))

theorem continuous_torusPt : Continuous (torusPt (K := K) (ι := ι)) :=
  continuous_pi fun i => GroundTheory.Global.continuous_infiniteAdeleInl.comp
    (continuous_ofCoord.comp (continuous_pi fun j => continuous_apply (i, j)))

theorem infiniteAdeleInl_algebraMap (y : InfiniteAdeleRing K) (a : K) :
    GroundTheory.Global.infiniteAdeleInl (y + algebraMap K (InfiniteAdeleRing K) a) =
      algebraMap K 𝔸[K] a + (GroundTheory.Global.infiniteAdeleInl y +
        GroundTheory.Global.finiteAdeleInr (-algebraMap K (FiniteAdeleRing (𝓞 K) K) a)) := by
  refine Prod.ext (α := InfiniteAdeleRing K) (β := FiniteAdeleRing (𝓞 K) K) ?_ ?_
  · show y + algebraMap K (InfiniteAdeleRing K) a = algebraMap K (InfiniteAdeleRing K) a + (y + 0)
    rw [add_zero, add_comm]
  · show (0 : FiniteAdeleRing (𝓞 K) K) = algebraMap K (FiniteAdeleRing (𝓞 K) K) a +
      (0 + -algebraMap K (FiniteAdeleRing (𝓞 K) K) a)
    rw [zero_add, add_neg_cancel]

theorem algebraMap_integer_mem_integralFiniteAdeles (a : 𝓞 K) :
    algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K a) ∈
      GroundTheory.Global.integralFiniteAdeles (𝓞 K) K :=
  fun v => GroundTheory.Global.coe_algebraMap_mem_adicCompletionIntegers v a

structure IsIntegralPeriodic (f : (ι → 𝔸[K]) → ℂ) : Prop where
  continuous : Continuous f
  periodic : ∀ ξ ∈ vecLattice K ι, ∀ x, f (ξ + x) = f x
  finite : ∀ x (z : ι → FiniteAdeleRing (𝓞 K) K),
    (∀ i, z i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) →
      f (x + fun i => GroundTheory.Global.finiteAdeleInr (z i)) = f x

theorem IsIntegralPeriodic.apply_torusPt_add_intCast {f : (ι → 𝔸[K]) → ℂ}
    (hf : IsIntegralPeriodic f) (t : ι × BIdx K → ℝ) (n : ι × BIdx K → ℤ) :
    f (torusPt (t + fun p => (n p : ℝ))) = f (torusPt t) := by
  set a : ι → 𝓞 K := fun i => ∑ j, n (i, j) • RingOfIntegers.basis K j
  have e : torusPt (t + fun p => (n p : ℝ)) =
      (fun i => algebraMap K 𝔸[K] (algebraMap (𝓞 K) K (a i))) +
      (torusPt t + fun i => GroundTheory.Global.finiteAdeleInr
        (-algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K (a i)))) := by
    funext i
    simp only [torusPt, Pi.add_apply]
    rw [show (fun j => t (i, j) + (n (i, j) : ℝ)) = (fun j => t (i, j)) + fun j => (n (i, j) : ℝ)
      from rfl, ofCoord_add, ofCoord_intCast, infiniteAdeleInl_algebraMap]
  rw [e, hf.periodic _ (algebraMap_mem_vecLattice _), hf.finite _ _ fun i =>
    neg_mem (algebraMap_integer_mem_integralFiniteAdeles (a i))]

theorem IsIntegralPeriodic.factorsThrough {f : (ι → 𝔸[K]) → ℂ} (hf : IsIntegralPeriodic f) :
    Function.FactorsThrough (fun t => f (torusPt t))
      (GroundTheory.Global.LatticePoisson.toTorus (ι := ι × BIdx K)) := by
  intro x y hxy
  have hk : ∀ p, ∃ k : ℤ, y p = x p + k := by
    intro p
    have hp : ((x p : ℝ) : UnitAddCircle) = (y p : UnitAddCircle) := congrFun hxy p
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp hp)
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    linarith
  choose k hk using hk
  have hy : y = x + fun p => (k p : ℝ) := funext fun p => by simp [hk]
  show f (torusPt x) = f (torusPt y)
  rw [hy, hf.apply_torusPt_add_intCast]

def IsIntegralPeriodic.torusFun {f : (ι → 𝔸[K]) → ℂ} (hf : IsIntegralPeriodic f) :
    C(UnitAddTorus (ι × BIdx K), ℂ) :=
  GroundTheory.Global.LatticePoisson.isQuotientMap_toTorus.lift
    ⟨fun t => f (torusPt t), hf.continuous.comp continuous_torusPt⟩ hf.factorsThrough

theorem IsIntegralPeriodic.torusFun_toTorus {f : (ι → 𝔸[K]) → ℂ} (hf : IsIntegralPeriodic f)
    (t : ι × BIdx K → ℝ) :
    hf.torusFun (GroundTheory.Global.LatticePoisson.toTorus t) = f (torusPt t) :=
  DFunLike.congr_fun (GroundTheory.Global.LatticePoisson.isQuotientMap_toTorus.lift_comp
    (⟨fun t => f (torusPt t), hf.continuous.comp continuous_torusPt⟩ : C(ι × BIdx K → ℝ, ℂ))
    hf.factorsThrough) t

theorem pair_torusPt (ξ : ι → K) (t : ι × BIdx K → ℝ) :
    pair ξ (torusPt t) = GroundTheory.Global.infiniteAdeleInl
      (∑ i, algebraMap K (InfiniteAdeleRing K) (ξ i) * ofCoord fun j => t (i, j)) := by
  simp only [pair, torusPt, GroundTheory.Global.algebraMap_mul_infiniteAdeleInl, map_sum]

theorem adelicChar_neg_pair_dualVec_torusPt (n : ι × BIdx K → ℤ) (t : ι × BIdx K → ℝ) :
    (GroundTheory.Global.adelicChar K (-pair (dualVec n) (torusPt t)) : ℂ) =
      UnitAddTorus.mFourier n (GroundTheory.Global.LatticePoisson.toTorus t) := by
  rw [pair_torusPt, ← map_neg, GroundTheory.Global.LatticePoisson.mFourier_toTorus]
  have := GroundTheory.Global.adelicChar_infinite (K := K)
    (-∑ i, algebraMap K (InfiniteAdeleRing K) (dualVec n i) * ofCoord fun j => t (i, j))
  refine (congrArg (fun z : Circle => (z : ℂ)) this).trans ?_
  congr 2
  rw [map_neg (GroundTheory.Global.infiniteTrace K), neg_neg, map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [infiniteTrace_algebraMap_mul_ofCoord]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [trace_dualVec_mul]
  push_cast
  ring

theorem IsIntegralPeriodic.integrand_finite {f : (ι → 𝔸[K]) → ℂ} (hf : IsIntegralPeriodic f)
    {ξ : ι → K} (hξ : IsDual ξ) (x : ι → 𝔸[K]) {z : ι → FiniteAdeleRing (𝓞 K) K}
    (hz : ∀ i, z i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) :
    f (x + fun i => GroundTheory.Global.finiteAdeleInr (z i)) *
        (GroundTheory.Global.adelicChar K (-pair ξ (x + fun i => GroundTheory.Global.finiteAdeleInr (z i))) : ℂ) =
      f x * (GroundTheory.Global.adelicChar K (-pair ξ x) : ℂ) := by
  have h1 : GroundTheory.Global.adelicChar K (-pair ξ fun i => GroundTheory.Global.finiteAdeleInr (z i)) = 1 := by
    rw [← pair_neg]
    have : (-fun i => GroundTheory.Global.finiteAdeleInr (z i)) =
        fun i => GroundTheory.Global.finiteAdeleInr (-z i) := by
      funext i; simp
    rw [this]
    exact adelicChar_pair_finiteAdeleInr hξ fun i => neg_mem (hz i)
  rw [hf.finite x z hz, pair_add, neg_add, AddChar.map_add_eq_mul, h1, mul_one]

variable (K ι) in

def infDomain : Set (ι → InfiniteAdeleRing K) :=
  Set.univ.pi fun _ => GroundTheory.Global.fundamentalSetInfinite K

variable (K ι) in

def finDomain : Set (ι → FiniteAdeleRing (𝓞 K) K) :=
  Set.univ.pi fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K))

theorem measurableSet_fundamentalSetInfinite :
    MeasurableSet (GroundTheory.Global.fundamentalSetInfinite K) := by
  rcases measurableSet_prod.1 (GroundTheory.Global.measurableSet_fundamentalSet K) with h | h | h
  · exact h.1
  · rw [h]; exact MeasurableSet.empty
  · have h0 : (0 : FiniteAdeleRing (𝓞 K) K) ∈ (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K :
        Set (FiniteAdeleRing (𝓞 K) K)) := zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K)
    rw [h] at h0
    exact absurd h0 (Set.notMem_empty _)

theorem setIntegral_vecDomain_eq {g : (ι → 𝔸[K]) → ℂ}
    (hg : ∀ x (z : ι → FiniteAdeleRing (𝓞 K) K),
      (∀ i, z i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) →
        g (x + fun i => GroundTheory.Global.finiteAdeleInr (z i)) = g x) :
    ∫ x in vecDomain K ι, g x ∂vecMeasure K ι =
      ((Measure.pi fun _ : ι => GroundTheory.Global.finiteAdeleMeasure K) (finDomain K ι)).toReal *
        ∫ y in infDomain K ι, g (fun i => GroundTheory.Global.infiniteAdeleInl (y i))
          ∂Measure.pi fun _ : ι => GroundTheory.Global.infiniteAdeleMeasure K := by
  let e : (ι → 𝔸[K]) ≃ᵐ (ι → InfiniteAdeleRing K) × (ι → FiniteAdeleRing (𝓞 K) K) :=
    MeasurableEquiv.arrowProdEquivProdArrow (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) ι
  have hmp : MeasurePreserving e (vecMeasure K ι)
      ((Measure.pi fun _ : ι => GroundTheory.Global.infiniteAdeleMeasure K).prod
        (Measure.pi fun _ : ι => GroundTheory.Global.finiteAdeleMeasure K)) :=
    measurePreserving_arrowProdEquivProdArrow (InfiniteAdeleRing K)
      (FiniteAdeleRing (𝓞 K) K) ι (fun _ => GroundTheory.Global.infiniteAdeleMeasure K)
      (fun _ => GroundTheory.Global.finiteAdeleMeasure K)
  have hpre : e ⁻¹' (infDomain K ι ×ˢ finDomain K ι) = vecDomain K ι := by
    ext x
    simp only [e, infDomain, finDomain, vecDomain, GroundTheory.Global.fundamentalSet,
      MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow, Set.mem_preimage,
      Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, SetLike.mem_coe]
    exact ⟨fun ⟨h1, h2⟩ i _ => ⟨h1 i, h2 i⟩,
      fun h => ⟨fun i => (h i (mem_univ i)).1, fun i => (h i (mem_univ i)).2⟩⟩
  have hsymm : ∀ p : (ι → InfiniteAdeleRing K) × (ι → FiniteAdeleRing (𝓞 K) K),
      (e.symm p : ι → 𝔸[K]) = (fun i => GroundTheory.Global.infiniteAdeleInl (p.1 i)) +
        fun i => GroundTheory.Global.finiteAdeleInr (p.2 i) := by
    intro p
    funext i
    refine Prod.ext (α := InfiniteAdeleRing K) (β := FiniteAdeleRing (𝓞 K) K) ?_ ?_
    · show p.1 i = p.1 i + 0
      rw [add_zero]
    · show p.2 i = 0 + p.2 i
      rw [zero_add]
  rw [← hpre]
  have h1 := hmp.setIntegral_preimage_emb e.measurableEmbedding (fun p => g (e.symm p))
    (infDomain K ι ×ˢ finDomain K ι)
  simp only [e.symm_apply_apply] at h1
  rw [h1]
  have hms : MeasurableSet (infDomain K ι ×ˢ finDomain K ι) := by
    refine (MeasurableSet.univ_pi fun _ => ?_).prod (MeasurableSet.univ_pi fun _ => ?_)
    · exact measurableSet_fundamentalSetInfinite
    · exact GroundTheory.Global.isOpen_integralFiniteAdeles.measurableSet
  rw [setIntegral_congr_fun hms (g := fun p => g (fun i => GroundTheory.Global.infiniteAdeleInl (p.1 i)) *
    (fun _ => (1 : ℂ)) p.2) fun p hp => by
      simp only [mul_one]
      rw [hsymm p]
      exact hg _ _ fun i => hp.2 i (mem_univ i)]
  rw [setIntegral_prod_mul (fun y : ι → InfiniteAdeleRing K => g fun i =>
    GroundTheory.Global.infiniteAdeleInl (y i)) (fun _ => (1 : ℂ)), setIntegral_const, mul_comm,
    measureReal_def]
  simp

def coordEquiv : (ι × BIdx K → ℝ) ≃+ (ι → InfiniteAdeleRing K) where
  toFun t i := ofCoord fun j => t (i, j)
  invFun y p := coordOf (y p.1) p.2
  left_inv t := by
    funext p
    show coordOf (ofCoord fun j => t (p.1, j)) p.2 = t p
    rw [coordOf_ofCoord]
  right_inv y := by
    funext i
    show ofCoord (fun j => coordOf (y i) j) = y i
    exact ofCoord_coordOf (y i)
  map_add' s t := by
    funext i
    exact ofCoord_add (fun j => s (i, j)) (fun j => t (i, j))

theorem coordEquiv_apply (t : ι × BIdx K → ℝ) (i : ι) :
    coordEquiv t i = ofCoord fun j => t (i, j) := rfl

theorem continuous_coordEquiv : Continuous (coordEquiv (K := K) (ι := ι)) :=
  continuous_pi fun i => continuous_ofCoord.comp (continuous_pi fun j => continuous_apply (i, j))

theorem continuous_coordEquiv_symm : Continuous (coordEquiv (K := K) (ι := ι)).symm :=
  continuous_pi fun p => (continuous_apply p.2).comp (continuous_coordOf.comp (continuous_apply p.1))

variable (K ι) in

def cube : Set (ι × BIdx K → ℝ) := {t | ∀ p, t p ∈ Ico (0 : ℝ) 1}

theorem coordEquiv_preimage_infDomain :
    coordEquiv ⁻¹' infDomain K ι = cube K ι := by
  ext t
  simp only [Set.mem_preimage, infDomain, Set.mem_pi, Set.mem_univ, true_implies,
    mem_fundamentalSetInfinite_iff, coordEquiv_apply, coordOf_ofCoord, cube, Set.mem_ofPred_eq]
  exact ⟨fun h p => h p.1 p.2, fun h i j => h (i, j)⟩

theorem volume_cube : volume (cube K ι) = 1 := by
  have : cube K ι = Set.pi univ (fun _ => Ico (0 : ℝ) 1) := by ext; simp [cube]
  rw [this, Real.volume_pi_Ico]
  simp

theorem setIntegral_infDomain_eq (g : (ι → InfiniteAdeleRing K) → ℂ) :
    ∫ y in infDomain K ι, g y ∂Measure.pi (fun _ : ι => GroundTheory.Global.infiniteAdeleMeasure K) =
      ((Measure.pi fun _ : ι => GroundTheory.Global.infiniteAdeleMeasure K) (infDomain K ι)).toReal *
        ∫ t in cube K ι, g (coordEquiv t) := by
  set μ := Measure.pi fun _ : ι => GroundTheory.Global.infiniteAdeleMeasure K
  let Te : (ι × BIdx K → ℝ) ≃ₜ (ι → InfiniteAdeleRing K) :=
    { toEquiv := coordEquiv.toEquiv, continuous_toFun := continuous_coordEquiv,
      continuous_invFun := continuous_coordEquiv_symm }
  have hme : MeasurableEmbedding Te := Te.measurableEmbedding
  set ν := (volume : Measure (ι × BIdx K → ℝ)).map Te
  have : ν.IsAddHaarMeasure := coordEquiv.isAddHaarMeasure_map volume continuous_coordEquiv
    continuous_coordEquiv_symm
  have hν : ν = ν.addHaarScalarFactor μ • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  have hpre : Te ⁻¹' infDomain K ι = cube K ι := coordEquiv_preimage_infDomain
  have hA : MeasurableSet (infDomain K ι) :=
    MeasurableSet.univ_pi fun _ => measurableSet_fundamentalSetInfinite
  have hνA : ν (infDomain K ι) = 1 := by
    rw [hme.map_apply, hpre, volume_cube]
  have hc : (ν.addHaarScalarFactor μ : ℝ) * (μ (infDomain K ι)).toReal = 1 := by
    have h := hνA
    rw [hν, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    have h2 := congrArg ENNReal.toReal h
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_one] at h2
  have hint : ∫ y in infDomain K ι, g y ∂ν = ∫ t in cube K ι, g (coordEquiv t) := by
    rw [hme.setIntegral_map, hpre]
    rfl
  have hsm : ∫ y in infDomain K ι, g y ∂ν =
      (ν.addHaarScalarFactor μ : ℝ) • ∫ y in infDomain K ι, g y ∂μ := by
    conv_lhs => rw [hν]
    rw [Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def]
  rw [← hint, hsm]
  have : ((μ (infDomain K ι)).toReal : ℂ) * ((ν.addHaarScalarFactor μ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_comm, hc, Complex.ofReal_one]
  rw [Complex.real_smul, ← mul_assoc, this, one_mul]

theorem measure_finDomain_mul_measure_infDomain :
    ((Measure.pi fun _ : ι => GroundTheory.Global.finiteAdeleMeasure K) (finDomain K ι)).toReal *
      ((Measure.pi fun _ : ι => GroundTheory.Global.infiniteAdeleMeasure K) (infDomain K ι)).toReal = 1 := by
  rw [← ENNReal.toReal_mul, finDomain, infDomain, Measure.pi_pi, Measure.pi_pi,
    ← Finset.prod_mul_distrib]
  have : ∀ i : ι, GroundTheory.Global.finiteAdeleMeasure K
      (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) *
      GroundTheory.Global.infiniteAdeleMeasure K (GroundTheory.Global.fundamentalSetInfinite K) = 1 := by
    intro i
    rw [mul_comm, ← GroundTheory.Global.adeleMeasure_prod]
    exact GroundTheory.Global.adeleMeasure_fundamentalSet K
  rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_const_one, ENNReal.toReal_one]

theorem IsIntegralPeriodic.vecCoeff_dualVec {f : (ι → 𝔸[K]) → ℂ} (hf : IsIntegralPeriodic f)
    (n : ι × BIdx K → ℤ) :
    vecCoeff f (dualVec n) = UnitAddTorus.mFourierCoeff hf.torusFun (-n) := by
  unfold vecCoeff
  rw [setIntegral_vecDomain_eq (g := fun x => f x *
      (GroundTheory.Global.adelicChar K (-pair (dualVec n) x) : ℂ))
      fun x z hz => hf.integrand_finite (isDual_dualVec n) x hz, setIntegral_infDomain_eq,
    ← mul_assoc, ← Complex.ofReal_mul, measure_finDomain_mul_measure_infDomain, Complex.ofReal_one,
    one_mul]
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ (-n) 0, neg_neg]
  have e1 : {x : ι × BIdx K → ℝ | ∀ i, x i ∈ Ioc ((0 : ι × BIdx K → ℝ) i)
      ((0 : ι × BIdx K → ℝ) i + 1)} =
      Set.pi univ (fun i => Ioc ((0 : ι × BIdx K → ℝ) i) ((1 : ι × BIdx K → ℝ) i)) := by
    ext; simp
  have e2 : cube K ι = Set.pi univ (fun i => Ico ((0 : ι × BIdx K → ℝ) i)
      ((1 : ι × BIdx K → ℝ) i)) := by
    ext; simp [cube]
  have hae : {x : ι × BIdx K → ℝ | ∀ i, x i ∈ Ioc ((0 : ι × BIdx K → ℝ) i)
      ((0 : ι × BIdx K → ℝ) i + 1)} =ᵐ[volume] cube K ι := by
    rw [e1, e2]
    exact Measure.univ_pi_Ioc_ae_eq_Icc.trans Measure.univ_pi_Ico_ae_eq_Icc.symm
  rw [setIntegral_congr_set hae]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  show f (torusPt t) * (GroundTheory.Global.adelicChar K (-pair (dualVec n) (torusPt t)) : ℂ) =
    UnitAddTorus.mFourier n (GroundTheory.Global.LatticePoisson.toTorus t) •
      hf.torusFun (GroundTheory.Global.LatticePoisson.toTorus t)
  rw [adelicChar_neg_pair_dualVec_torusPt, hf.torusFun_toTorus, smul_eq_mul, mul_comm]

theorem dualVec_neg (n : ι × BIdx K → ℤ) : dualVec (-n) = -dualVec n := by
  funext i
  simp [dualVec, Finset.sum_neg_distrib]

theorem pair_neg_left (ξ : ι → K) (x : ι → 𝔸[K]) : pair (-ξ) x = -pair ξ x := by
  simp [pair, Finset.sum_neg_distrib]

theorem IsIntegralPeriodic.hasSum_vecCoeff {f : (ι → 𝔸[K]) → ℂ} (hf : IsIntegralPeriodic f)
    (hsum : Summable (vecCoeff f)) (x : ι → 𝔸[K]) :
    HasSum (fun ξ => vecCoeff f ξ * (GroundTheory.Global.adelicChar K (pair ξ x) : ℂ)) (f x) := by
  choose l hl using fun i => GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (R := 𝓞 K) (x i).2
  set y : ι → InfiniteAdeleRing K := fun i => (x i).1 - algebraMap K (InfiniteAdeleRing K) (l i)
  set t := coordEquiv.symm y
  have ht : torusPt t = fun i => GroundTheory.Global.infiniteAdeleInl (y i) := by
    funext i
    show GroundTheory.Global.infiniteAdeleInl (coordEquiv t i) = _
    rw [AddEquiv.apply_symm_apply]
  set z : ι → FiniteAdeleRing (𝓞 K) K :=
    fun i => (x i).2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) (l i)
  have hx : x = (fun i => algebraMap K 𝔸[K] (l i)) +
      (torusPt t + fun i => GroundTheory.Global.finiteAdeleInr (z i)) := by
    rw [ht]
    funext i
    refine Prod.ext (α := InfiniteAdeleRing K) (β := FiniteAdeleRing (𝓞 K) K) ?_ ?_
    · show (x i).1 = algebraMap K (InfiniteAdeleRing K) (l i) + (y i + 0)
      simp [y]
    · show (x i).2 = algebraMap K (FiniteAdeleRing (𝓞 K) K) (l i) + (0 + z i)
      simp [z]
  have hfx : f x = hf.torusFun (GroundTheory.Global.LatticePoisson.toTorus t) := by
    rw [hf.torusFun_toTorus, hx, hf.periodic _ (algebraMap_mem_vecLattice _), hf.finite _ _ hl]
  have hcoeff : UnitAddTorus.mFourierCoeff hf.torusFun = fun m => vecCoeff f (dualVec (-m)) :=
    funext fun m => by rw [hf.vecCoeff_dualVec, neg_neg]
  have hsumT : Summable (UnitAddTorus.mFourierCoeff hf.torusFun) := by
    rw [hcoeff]
    exact hsum.comp_injective (dualVec_injective.comp neg_injective)
  have h1 := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsumT
    (GroundTheory.Global.LatticePoisson.toTorus t)
  have h2 := (Equiv.neg (ι × BIdx K → ℤ)).hasSum_iff.2 h1
  have hchar : ∀ n : ι × BIdx K → ℤ, (GroundTheory.Global.adelicChar K (pair (dualVec n) x) : ℂ) =
      UnitAddTorus.mFourier (-n) (GroundTheory.Global.LatticePoisson.toTorus t) := by
    intro n
    have hz : GroundTheory.Global.adelicChar K (pair (dualVec n) fun i => GroundTheory.Global.finiteAdeleInr (z i)) =
        1 := adelicChar_pair_finiteAdeleInr (isDual_dualVec n) hl
    rw [hx, pair_add, pair_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      adelicChar_pair_of_mem _ (algebraMap_mem_vecLattice _), hz, one_mul, mul_one,
      ← adelicChar_neg_pair_dualVec_torusPt, dualVec_neg, pair_neg_left, neg_neg]
  have h3 : HasSum (fun n => vecCoeff f (dualVec n) *
      (GroundTheory.Global.adelicChar K (pair (dualVec n) x) : ℂ)) (f x) := by
    rw [hfx]
    convert h2 using 1
    funext n
    simp only [Function.comp_apply, Equiv.neg_apply, hchar, smul_eq_mul, hcoeff, neg_neg]
  refine (dualVec_injective.hasSum_iff fun ξ hξ => ?_).1 h3
  have hnd : ¬ IsDual ξ := fun hd => hξ (exists_dualVec_eq hd)
  rw [vecCoeff_eq_zero_of_not_isDual hf.periodic hf.finite hnd, zero_mul]

end FourierWhittaker

end

end GroundTheory.Automorphic
