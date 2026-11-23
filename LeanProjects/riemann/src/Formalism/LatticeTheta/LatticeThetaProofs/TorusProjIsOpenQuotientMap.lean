import Formalism.LatticeTheta.LatticeThetaProofs.InnerDualVecBasis
import Formalism.LatticeTheta.LatticeThetaProofs.FundamentalDomainEqPreimage

open MeasureTheory Set Complex
open scoped RealInnerProductSpace

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def torusProj (ι : Type*) : (ι → ℝ) → UnitAddTorus ι := fun t i => (t i : UnitAddCircle)

theorem torusProj_isOpenQuotientMap : IsOpenQuotientMap (torusProj ι) :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

theorem torusProj_surjective : Function.Surjective (torusProj ι) := by
  intro θ
  choose t ht using fun i => QuotientAddGroup.mk_surjective (θ i)
  exact ⟨t, funext ht⟩

theorem torusProj_eq (s t : ι → ℝ) (h : torusProj ι s = torusProj ι t) :
    ∃ n : ι → ℤ, t = s + fun i => (n i : ℝ) := by
  have hi : ∀ i, ∃ k : ℤ, t i = s i + (k : ℝ) := by
    intro i
    have h1 := congrFun h i
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp h1)
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    linarith
  choose n hn using hi
  exact ⟨n, funext fun i => by simp [hn i]⟩

theorem equivFunL_symm_eq (e : Module.Basis ι ℝ V) (t : ι → ℝ) :
    e.equivFunL.symm t = ∑ i, t i • e i := by
  first
  | exact e.equivFun_symm_apply t
  | simp [Module.Basis.equivFunL, Module.Basis.equivFun_symm_apply]

theorem periodic_comp (e : Module.Basis ι ℝ V) (G : V → ℂ)
    (hper : ∀ l ∈ Submodule.span ℤ (Set.range e), ∀ x, G (l + x) = G x)
    (s : ι → ℝ) (n : ι → ℤ) :
    G (e.equivFunL.symm (s + fun i => (n i : ℝ))) = G (e.equivFunL.symm s) := by
  rw [map_add, add_comm]
  apply hper
  rw [equivFunL_symm_eq]
  refine Submodule.sum_mem _ fun i _ => ?_
  show ((n i : ℝ)) • e i ∈ _
  rw [Int.cast_smul_eq_zsmul ℝ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def torusFun (e : Module.Basis ι ℝ V) (G : V → ℂ) : UnitAddTorus ι → ℂ :=
  fun θ => G (e.equivFunL.symm (Function.surjInv (torusProj_surjective (ι := ι)) θ))

theorem torusFun_proj (e : Module.Basis ι ℝ V) (G : V → ℂ)
    (hper : ∀ l ∈ Submodule.span ℤ (Set.range e), ∀ x, G (l + x) = G x) (t : ι → ℝ) :
    torusFun e G (torusProj ι t) = G (e.equivFunL.symm t) := by
  obtain ⟨n, hn⟩ := torusProj_eq _ t
    (Function.surjInv_eq (torusProj_surjective (ι := ι)) (torusProj ι t))
  have h1 := periodic_comp e G hper (Function.surjInv (torusProj_surjective (ι := ι)) (torusProj ι t)) n
  rw [← hn] at h1
  exact h1.symm

theorem torusFun_continuous (e : Module.Basis ι ℝ V) (G : V → ℂ) (hG : Continuous G)
    (hper : ∀ l ∈ Submodule.span ℤ (Set.range e), ∀ x, G (l + x) = G x) :
    Continuous (torusFun e G) := by
  rw [torusProj_isOpenQuotientMap.isQuotientMap.continuous_iff]
  have h1 : torusFun e G ∘ torusProj ι = fun t => G (e.equivFunL.symm t) :=
    funext (torusFun_proj e G hper)
  rw [h1]
  exact hG.comp e.equivFunL.symm.continuous

def torusFunC (e : Module.Basis ι ℝ V) (G : V → ℂ) (hG : Continuous G)
    (hper : ∀ l ∈ Submodule.span ℤ (Set.range e), ∀ x, G (l + x) = G x) :
    C(UnitAddTorus ι, ℂ) :=
  ⟨torusFun e G, torusFun_continuous e G hG hper⟩

theorem mFourier_torusProj (e : Module.Basis ι ℝ V) (m : ι → ℤ) (t : ι → ℝ) :
    UnitAddTorus.mFourier m (torusProj ι t) =
      Complex.exp (2 * Real.pi * Complex.I * (⟪dualVec e m, e.equivFunL.symm t⟫ : ℝ)) := by
  have hinner : (⟪dualVec e m, e.equivFunL.symm t⟫ : ℝ) = ∑ i, (m i : ℝ) * t i := by
    rw [equivFunL_symm_eq, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_right, inner_dualVec_basis, mul_comm]
  rw [hinner]
  show (∏ i, fourier (m i) ((t i : ℝ) : UnitAddCircle)) = _
  rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem boxIoc_ae_eq :
    ({x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} : Set (ι → ℝ))
      =ᵐ[volume] boxIco ι := by
  have h1 : ({x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} : Set (ι → ℝ)) =
      Set.univ.pi fun i => Ioc ((0 : ι → ℝ) i) ((1 : ι → ℝ) i) := by
    ext x
    simp [Set.mem_univ_pi]
  rw [h1]
  show _ =ᵐ[Measure.pi fun _ => volume] _
  exact Measure.univ_pi_Ioc_ae_eq_Icc.trans Measure.univ_pi_Ico_ae_eq_Icc.symm

theorem mFourierCoeff_torusFunC (e : Module.Basis ι ℝ V) (G : V → ℂ) (hG : Continuous G)
    (hper : ∀ l ∈ Submodule.span ℤ (Set.range e), ∀ x, G (l + x) = G x) (m : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (torusFunC e G hG hper) m =
      ∫ t in boxIco ι, G (e.equivFunL.symm t) *
        Complex.exp (-(2 * Real.pi * Complex.I * (⟪dualVec e m, e.equivFunL.symm t⟫ : ℝ))) := by
  have hS : (Set.univ.pi fun _ : ι => Ioc (0 : ℝ) (0 + 1)) =
      {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} := by
    ext x
    simp [Set.mem_univ_pi]
  have hmp : MeasurePreserving (torusProj ι)
      (volume.restrict {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)})
      (@volume (UnitAddTorus ι)
        (@MeasureSpace.pi ι _ (fun _ => UnitAddCircle) fun _ => instMeasureSpaceUnitAddCircle)) := by
    have hvol : @volume UnitAddCircle instMeasureSpaceUnitAddCircle =
        @volume UnitAddCircle (AddCircle.measureSpace 1) := by
      first
      | rfl
      | (rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; rfl)
      | (simp [AddCircle.volume_eq_smul_haarAddCircle])
      | (rw [AddCircle.volume_eq_smul_haarAddCircle]; simp)
    rw [← hS]
    show MeasurePreserving _ ((Measure.pi fun _ => volume).restrict _)
      (Measure.pi fun _ => @volume UnitAddCircle instMeasureSpaceUnitAddCircle)
    rw [Measure.restrict_pi_pi, hvol]
    exact measurePreserving_pi (μ := fun _ => volume.restrict (Ioc (0 : ℝ) (0 + 1)))
      (ν := fun _ => @volume UnitAddCircle (AddCircle.measureSpace 1))
      (fun _ => AddCircle.measurePreserving_mk 1 0)
  have hneg : dualVec e (-m) = -dualVec e m := by
    simp only [dualVec, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
  have hmap := integral_map (f := fun θ => UnitAddTorus.mFourier (-m) θ • torusFunC e G hG hper θ)
    hmp.aemeasurable
    ((UnitAddTorus.mFourier (-m)).continuous.smul (torusFunC e G hG hper).continuous).aestronglyMeasurable
  rw [hmp.map_eq] at hmap
  rw [UnitAddTorus.mFourierCoeff]
  refine hmap.trans ?_
  rw [Measure.restrict_congr_set boxIoc_ae_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show UnitAddTorus.mFourier (-m) (torusProj ι t) * torusFun e G (torusProj ι t) = _
  rw [torusFun_proj e G hper, mFourier_torusProj e (-m) t, mul_comm, hneg, inner_neg_left]
  congr 1
  push_cast
  ring
  all_goals first | infer_instance | assumption

end Formalism.H
