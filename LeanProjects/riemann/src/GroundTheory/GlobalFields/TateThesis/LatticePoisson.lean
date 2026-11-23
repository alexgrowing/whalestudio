import Mathlib
import GroundTheory.GlobalFields.TateThesis.LatticePoissonBasic

namespace GroundTheory.Global

open MeasureTheory Module Set Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap

noncomputable section

theorem fourierChar_add_intCast (x : ℝ) (k : ℤ) : 𝐞 (x + k) = 𝐞 x := by
  rw [AddChar.map_add_eq_mul]
  have : 𝐞 (k : ℝ) = 1 := by
    ext
    rw [Real.fourierChar_apply, Circle.coe_one]
    convert Complex.exp_int_mul_two_pi_mul_I k using 2
    push_cast
    ring
  rw [this, mul_one]

namespace LatticePoisson

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)

def dualB : Basis ι ℝ E :=
  LinearMap.BilinForm.dualBasis (innerₗ E) innerₗ_nondegenerate (b.ofZLatticeBasis ℝ L)

theorem inner_dualB (i j : ι) :
    ⟪dualB b i, b.ofZLatticeBasis ℝ L j⟫ = if j = i then 1 else 0 :=
  LinearMap.BilinForm.apply_dualBasis_left innerₗ_nondegenerate _ i j

def dualPt (m : ι → ℤ) : E := ∑ i, (m i : ℝ) • dualB b i

theorem inner_dualPt_basis (m : ι → ℤ) (j : ι) :
    ⟪dualPt b m, b.ofZLatticeBasis ℝ L j⟫ = m j := by
  simp only [dualPt, sum_inner, real_inner_smul_left, inner_dualB, mul_ite, mul_one, mul_zero]
  simp

theorem inner_equivFun_symm_dualPt (x : ι → ℝ) (m : ι → ℤ) :
    ⟪(b.ofZLatticeBasis ℝ L).equivFun.symm x, dualPt b m⟫ = ∑ i, (m i : ℝ) * x i := by
  rw [Basis.equivFun_symm_apply, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, real_inner_comm, inner_dualPt_basis, mul_comm]

theorem inner_dualPt_mem (m : ι → ℤ) (ℓ : L) :
    ⟪dualPt b m, (ℓ : E)⟫ = ((∑ i, m i * b.repr ℓ i : ℤ) : ℝ) := by
  conv_lhs => rw [← (b.ofZLatticeBasis ℝ L).sum_repr (ℓ : E)]
  rw [inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, inner_dualPt_basis, Basis.ofZLatticeBasis_repr_apply ℝ L b ℓ i]
  ring

theorem dualPt_mem (m : ι → ℤ) : dualPt b m ∈ dualLattice L :=
  mem_dualLattice.mpr fun ℓ hℓ => ⟨_, inner_dualPt_mem b m ⟨ℓ, hℓ⟩⟩

omit [Fintype ι] [DecidableEq ι] in
theorem basis_mem (j : ι) : b.ofZLatticeBasis ℝ L j ∈ L := by
  rw [Basis.ofZLatticeBasis_apply ℝ L b j]; exact (b j).2

def dualEquiv : (ι → ℤ) ≃ dualLattice L :=
  Equiv.ofBijective (fun m => ⟨dualPt b m, dualPt_mem b m⟩) ⟨fun m m' h => by
      funext j
      have : ⟪dualPt b m, b.ofZLatticeBasis ℝ L j⟫ = ⟪dualPt b m', b.ofZLatticeBasis ℝ L j⟫ :=
        congrArg (fun v : dualLattice L => ⟪(v : E), b.ofZLatticeBasis ℝ L j⟫) h
      rw [inner_dualPt_basis, inner_dualPt_basis] at this
      exact_mod_cast this,
    fun μ => by
      have hμ := mem_dualLattice.mp μ.2
      choose m hm using fun j => hμ _ (basis_mem b j)
      refine ⟨m, Subtype.ext ?_⟩
      change dualPt b m = (μ : E)
      conv_rhs => rw [← (dualB b).sum_repr (μ : E)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [dualB, LinearMap.BilinForm.dualBasis_repr_apply, innerₗ_apply_apply, hm]⟩

theorem coe_dualEquiv (m : ι → ℤ) : (dualEquiv b m : E) = dualPt b m := rfl

def toTorus : C(ι → ℝ, UnitAddTorus ι) :=
  ⟨fun x i => (x i : UnitAddCircle),
    continuous_pi fun i => continuous_quotient_mk'.comp (continuous_apply i)⟩

omit [Fintype ι] [DecidableEq ι] in
theorem isQuotientMap_toTorus : Topology.IsQuotientMap (toTorus (ι := ι)) :=
  (IsOpenQuotientMap.piMap (A := fun _ : ι => ℝ) (B := fun _ => UnitAddCircle)
    fun _ => QuotientAddGroup.isOpenQuotientMap_mk).isQuotientMap

omit [DecidableEq ι] in
theorem mFourier_toTorus (m : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier m (toTorus x) = 𝐞 (∑ i, (m i : ℝ) * x i) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, toTorus, fourier_coe_apply,
    Real.fourierChar_apply, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

def per (L : Submodule ℤ E) (f : 𝓢(E, ℂ)) (x : E) : ℂ := ∑' ℓ : L, f (x + ℓ)

omit [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] [Fintype ι] [DecidableEq ι] in
theorem per_add (f : 𝓢(E, ℂ)) (x : E) {v : E} (hv : v ∈ L) : per L f (x + v) = per L f x := by
  unfold per
  rw [← (Equiv.addLeft (⟨v, hv⟩ : L)).tsum_eq (fun ℓ : L => f (x + ℓ))]
  simp [add_assoc]

def perCoord (f : 𝓢(E, ℂ)) : C(ι → ℝ, ℂ) :=
  ⟨fun x => per L f ((b.ofZLatticeBasis ℝ L).equivFun.symm x),
    (continuous_tsum_comp_add L f).comp (LinearMap.continuous_of_finiteDimensional _)⟩

omit [DecidableEq ι] in
theorem perCoord_factorsThrough (f : 𝓢(E, ℂ)) :
    Function.FactorsThrough (perCoord b f) (toTorus (ι := ι)) := by
  intro x y hxy
  have hk : ∀ i, ∃ k : ℤ, y i = x i + k := by
    intro i
    have hi : ((x i : ℝ) : UnitAddCircle) = (y i : UnitAddCircle) := congrFun hxy i
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp hi)
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    linarith
  choose k hk using hk
  have hy : y = x + fun i => (k i : ℝ) := funext fun i => by simp [hk]
  have hmem : (b.ofZLatticeBasis ℝ L).equivFun.symm (fun i => (k i : ℝ)) ∈ L := by
    rw [Basis.equivFun_symm_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact zsmul_mem (basis_mem b i) _
  change per L f ((b.ofZLatticeBasis ℝ L).equivFun.symm x) =
    per L f ((b.ofZLatticeBasis ℝ L).equivFun.symm y)
  rw [hy, LinearEquiv.map_add]
  exact (per_add f _ hmem).symm

def perTorus (f : 𝓢(E, ℂ)) : C(UnitAddTorus ι, ℂ) :=
  isQuotientMap_toTorus.lift (perCoord b f) (perCoord_factorsThrough b f)

omit [DecidableEq ι] in
theorem perTorus_toTorus (f : 𝓢(E, ℂ)) (x : ι → ℝ) :
    perTorus b f (toTorus x) = per L f ((b.ofZLatticeBasis ℝ L).equivFun.symm x) :=
  DFunLike.congr_fun (isQuotientMap_toTorus.lift_comp (perCoord b f)
    (perCoord_factorsThrough b f)) x

variable [MeasurableSpace E] [BorelSpace E]

omit [DecidableEq ι] in

theorem integral_fundamentalDomain (f : 𝓢(E, ℂ)) {μ : E} (hμ : μ ∈ dualLattice L) :
    ∫ y in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L),
      (𝐞 (-⟪y, μ⟫) : ℂ) * ∑' ℓ : L, f (y + ℓ) = 𝓕 (f : E → ℂ) μ := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup E volume)
  have hD := ZLattice.isAddFundamentalDomain b (volume : Measure E)
  set D := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have hphase : ∀ (ℓ : L) (y : E), (𝐞 (-⟪(ℓ : E) + y, μ⟫) : ℂ) = 𝐞 (-⟪y, μ⟫) := by
    intro ℓ y
    obtain ⟨k, hk⟩ := (mem_dualLattice.mp hμ) ℓ ℓ.2
    rw [inner_add_left, real_inner_comm, hk, neg_add, add_comm, ← Int.cast_neg,
      fourierChar_add_intCast]
  have hint : Integrable (fun y => (𝐞 (-⟪y, μ⟫) : ℂ) * f y) := by
    have := (Real.fourierIntegral_convergent_iff (μ := volume) μ).mpr f.integrable
    simpa [Circle.smul_def] using this
  have hce : Continuous fun y : E => (𝐞 (-⟪y, μ⟫) : ℂ) := by fun_prop
  have hmeas : ∀ ℓ : L, AEStronglyMeasurable (fun y => (𝐞 (-⟪y, μ⟫) : ℂ) * f (ℓ + y))
      (volume.restrict D) := fun ℓ =>
    (hce.mul (f.continuous.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  have hfin : ∑' ℓ : L, ∫⁻ y in D, ‖(𝐞 (-⟪y, μ⟫) : ℂ) * f (ℓ + y)‖ₑ ≠ ⊤ := by
    have h1 : ∀ (ℓ : L) (y : E), ‖(𝐞 (-⟪y, μ⟫) : ℂ) * f (ℓ + y)‖ₑ = ‖f (ℓ + y)‖ₑ := by
      intro ℓ y
      rw [enorm_mul, ← ofReal_norm (𝐞 _ : ℂ), Circle.norm_coe, ENNReal.ofReal_one, one_mul]
    simp_rw [h1]
    have h2 := hD.lintegral_eq_tsum' (fun y => ‖f y‖ₑ)
    rw [← (Equiv.neg L).tsum_eq] at h2
    simp only [Equiv.neg_apply, neg_neg, Submodule.vadd_def, vadd_eq_add] at h2
    rw [← h2]
    exact f.integrable.2.ne
  rw [Real.fourier_eq]
  simp_rw [Circle.smul_def, smul_eq_mul]
  rw [hD.integral_eq_tsum'' _ hint]
  simp only [Submodule.vadd_def, vadd_eq_add, hphase]
  rw [← integral_tsum hmeas hfin]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [← tsum_mul_left]
  exact tsum_congr fun ℓ => by rw [add_comm y]

omit [DecidableEq ι] in

theorem setIntegral_cube (φ : E → ℂ) :
    ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1}, φ ((b.ofZLatticeBasis ℝ L).equivFun.symm x) =
      (ZLattice.covolume L)⁻¹ • ∫ y in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L), φ y := by
  set b₀ := b.ofZLatticeBasis ℝ L
  set D := ZSpan.fundamentalDomain b₀
  let T : (ι → ℝ) ≃L[ℝ] E := b₀.equivFun.symm.toContinuousLinearEquiv
  have hT : ∀ x, T x = b₀.equivFun.symm x := fun _ => rfl
  set ν := Measure.map T (volume : Measure (ι → ℝ))
  have : ν.IsAddHaarMeasure := T.isAddHaarMeasure_map volume
  have hpre : T ⁻¹' D = {x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1} := by
    ext x
    have : ∀ i, b₀.repr (b₀.equivFun.symm x) i = x i := fun i => by
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    simp only [Set.mem_preimage, D, ZSpan.mem_fundamentalDomain, hT, this, Set.mem_ofPred_eq]
  have hDm : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet b₀
  have hνD : ν D = 1 := by
    rw [Measure.map_apply T.continuous.measurable hDm, hpre]
    have : {x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1} =
        Set.pi univ (fun i => Ico ((0 : ι → ℝ) i) ((1 : ι → ℝ) i)) := by ext; simp
    rw [this, Real.volume_pi_Ico]
    simp
  have hcv : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  have hvolD : volume D = ENNReal.ofReal (ZLattice.covolume L) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume
      (ZLattice.isAddFundamentalDomain b volume), measureReal_def, ENNReal.ofReal_toReal]
    exact (ZSpan.fundamentalDomain_isBounded b₀).measure_lt_top.ne
  set c := ν.addHaarScalarFactor volume
  have hν : ν = c • volume := Measure.isAddLeftInvariant_eq_smul ν volume
  have hc : (c : ℝ) = (ZLattice.covolume L)⁻¹ := by
    have h1 := hνD
    rw [hν, Measure.smul_apply, hvolD, ENNReal.smul_def, smul_eq_mul] at h1
    have h2 := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal hcv.le,
      ENNReal.toReal_one] at h2
    exact eq_inv_of_mul_eq_one_left h2
  calc ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1}, φ (b₀.equivFun.symm x)
      = ∫ x in T ⁻¹' D, φ (T x) := by rw [hpre]; rfl
    _ = ∫ y in D, φ y ∂ν := (T.continuous.measurable.measurePreserving volume).setIntegral_preimage_emb
          T.toHomeomorph.measurableEmbedding φ D
    _ = (ZLattice.covolume L)⁻¹ • ∫ y in D, φ y := by
          rw [hν, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, hc]
  rfl

theorem mFourierCoeff_perTorus (f : 𝓢(E, ℂ)) (m : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (perTorus b f) m =
      (ZLattice.covolume L)⁻¹ • 𝓕 (f : E → ℂ) (dualPt b m) := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ m 0]
  have h1 : ∀ x : ι → ℝ, UnitAddTorus.mFourier (-m) (fun i => (x i : UnitAddCircle)) •
      perTorus b f (fun i => (x i : UnitAddCircle)) =
      (𝐞 (-⟪(b.ofZLatticeBasis ℝ L).equivFun.symm x, dualPt b m⟫) : ℂ) *
        ∑' ℓ : L, f ((b.ofZLatticeBasis ℝ L).equivFun.symm x + ℓ) := by
    intro x
    rw [show (fun i => (x i : UnitAddCircle)) = toTorus x from rfl, mFourier_toTorus,
      perTorus_toTorus, smul_eq_mul, inner_equivFun_symm_dualPt]
    simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, per]
  simp_rw [h1]
  have e1 : {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} =
      Set.pi univ (fun i => Ioc ((0 : ι → ℝ) i) ((1 : ι → ℝ) i)) := by ext; simp
  have e2 : {x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1} =
      Set.pi univ (fun i => Ico ((0 : ι → ℝ) i) ((1 : ι → ℝ) i)) := by ext; simp
  have hae : {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} =ᵐ[volume]
      {x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1} := by
    rw [e1, e2]
    exact Measure.univ_pi_Ioc_ae_eq_Icc.trans Measure.univ_pi_Ico_ae_eq_Icc.symm
  rw [setIntegral_congr_set hae,
    setIntegral_cube b (fun y => (𝐞 (-⟪y, dualPt b m⟫) : ℂ) * ∑' ℓ : L, f (y + ℓ)),
    integral_fundamentalDomain b f (dualPt_mem b m)]

theorem summable_norm_fourier (f : 𝓢(E, ℂ)) :
    Summable fun μ : dualLattice L => ‖𝓕 (f : E → ℂ) μ‖ := by
  simpa [SchwartzMap.fourier_coe] using summable_norm_comp_add (dualLattice L) (𝓕 f) 0

omit [DecidableEq ι] in
theorem summable_mFourierCoeff_perTorus (f : 𝓢(E, ℂ)) :
    Summable (UnitAddTorus.mFourierCoeff (perTorus b f)) := by
  classical
  have h : Summable fun μ : dualLattice L => 𝓕 (f : E → ℂ) μ := (summable_norm_fourier f).of_norm
  refine (((dualEquiv b).summable_iff.mpr h).const_smul (ZLattice.covolume L)⁻¹).congr
    fun m => ?_
  rw [mFourierCoeff_perTorus]
  rfl

theorem hasSum_smul_fourier (f : 𝓢(E, ℂ)) (a : E) :
    HasSum (fun μ : dualLattice L => (ZLattice.covolume L)⁻¹ • (𝓕 (f : E → ℂ) μ * 𝐞 ⟪(μ : E), a⟫))
      (per L f a) := by
  classical
  let b := Free.chooseBasis ℤ L
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (summable_mFourierCoeff_perTorus b f) (toTorus ((b.ofZLatticeBasis ℝ L).equivFun a))
  rw [perTorus_toTorus, LinearEquiv.symm_apply_apply] at h
  rw [← (dualEquiv b).hasSum_iff]
  convert h using 1
  funext m
  have hin : ⟪dualPt b m, a⟫ = ∑ i, (m i : ℝ) * (b.ofZLatticeBasis ℝ L).equivFun a i := by
    rw [real_inner_comm, ← inner_equivFun_symm_dualPt b, LinearEquiv.symm_apply_apply]
  simp only [Function.comp_apply, coe_dualEquiv, mFourierCoeff_perTorus, mFourier_toTorus, hin,
    smul_eq_mul, smul_mul_assoc]

end LatticePoisson

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] in

theorem lattice_summable_norm (f : 𝓢(E, ℂ)) (a : E) : Summable fun ℓ : L => ‖f (ℓ + a)‖ := by
  simpa [add_comm] using summable_norm_comp_add L f a

theorem dualLattice_summable_norm (f : 𝓢(E, ℂ)) (a : E) :
    Summable fun μ : dualLattice L => ‖𝓕 (f : E → ℂ) μ * 𝐞 ⟪(μ : E), a⟫‖ := by
  simpa [norm_mul, Circle.norm_coe] using LatticePoisson.summable_norm_fourier (L := L) f

theorem lattice_poisson_summation (f : 𝓢(E, ℂ)) (a : E) :
    ∑' ℓ : L, f (ℓ + a) =
      (ZLattice.covolume L)⁻¹ • ∑' μ : dualLattice L, 𝓕 (f : E → ℂ) μ * 𝐞 ⟪(μ : E), a⟫ := by
  rw [← tsum_const_smul'', (LatticePoisson.hasSum_smul_fourier (L := L) f a).tsum_eq,
    LatticePoisson.per]
  exact tsum_congr fun ℓ => by rw [add_comm]

theorem hasSum_lattice_poisson (f : 𝓢(E, ℂ)) (a : E) :
    HasSum (fun μ : dualLattice L => 𝓕 (f : E → ℂ) μ * 𝐞 ⟪(μ : E), a⟫)
      (ZLattice.covolume L • ∑' ℓ : L, f (ℓ + a)) := by
  rw [lattice_poisson_summation, smul_smul, mul_inv_cancel₀ (ZLattice.covolume_ne_zero L volume),
    one_smul]
  exact (dualLattice_summable_norm L f a).of_norm.hasSum

end Main

end

end GroundTheory.Global
