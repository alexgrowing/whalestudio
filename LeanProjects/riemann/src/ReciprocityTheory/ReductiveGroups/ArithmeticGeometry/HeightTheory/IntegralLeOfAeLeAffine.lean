import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UniformizerOfResidueIndep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GoodPrimesProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormPts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IntNsg
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FsumEqSum

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

open MeasureTheory

theorem be_pos (hd : d.AxH 𝒜) (c : ι) (P : Ω c →+* ℂ) : 0 < d.be c P := by
  unfold Data.be
  apply Real.sqrt_pos.mpr
  have h1 := hd.nrm_pos c P (hd.w_mem (d.jc c) c) (hd.w_base c)
  exact lt_of_lt_of_le (pow_pos h1 2)
    (Finset.single_le_sum (f := fun j => d.nrm c d.wL (d.w j c) P ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ (d.jc c)))

theorem fneg {α : Type*} (s : Set α) (g : α → ℝ) : ∑ᶠ x ∈ s, -g x = -∑ᶠ x ∈ s, g x := by
  simp only [finsum_neg_distrib]

theorem integral_le_of_ae_le_affine {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (F1 F2 F3 : X → ℝ) (C r : ℝ) (I1 : Integrable F1 μ) (I2 : Integrable F2 μ) (I3 : Integrable F3 μ)
    (hle : ∀ᵐ x ∂μ, F1 x ≤ F2 x + C + r * F3 x) :
    ∫ x, F1 x ∂μ ≤ ∫ x, F2 x ∂μ + C + r * ∫ x, F3 x ∂μ := by
  have hC : Integrable (fun _ : X => C) μ := integrable_const C
  have h2C : Integrable (fun x => F2 x + C) μ := I2.add hC
  have hI : Integrable (fun x => F2 x + C + r * F3 x) μ := h2C.add (I3.const_mul r)
  calc ∫ x, F1 x ∂μ ≤ ∫ x, (F2 x + C + r * F3 x) ∂μ := integral_mono_ae I1 hI hle
    _ = ∫ x, F2 x ∂μ + C + r * ∫ x, F3 x ∂μ := by
      rw [integral_add h2C (I3.const_mul r), integral_const_mul, integral_add I2 hC]
      simp

theorem int_neg (c : ι) (sg : K →+* ℂ) (g : (Ω c →+* ℂ) → ℝ)
    (hI : Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
      ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)), g P)
      (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))) :
    Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
      ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)), -g P)
      (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  exact hI.neg.congr (ae_of_all _ fun z => by simp only [Pi.neg_apply, fneg])

theorem sg_one (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) (c : ι) (sg : K →+* ℂ) :
    ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
      -Real.log (d.nrm c d.wL (f c) P)) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) ≤
    ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
      -Real.log (d.nrm c d.wL (f c) P / d.be c P)) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) +
    d.delc c * (d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo) + d.cc / d.i *
    ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
      -Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  haveI := ReciprocityTheory.MultiplicativeHeights.blockSphereMeasure_isProbability (B := d.D) (Nat.succ_pos d.N)
  have hint := d.int_Nsg hd h hI2be c sg
  have I1 := d.int_neg c sg (fun P => Real.log (d.nrm c d.wL (f c) P))
    (hint.1 d.wL (f c) (by simp) (hf c).1 (hf c).2)
  have I2 := d.int_neg c sg (fun P => Real.log (d.nrm c d.wL (f c) P / d.be c P))
    (hint.2 (f c) (hf c).1 (hf c).2)
  have I3 := d.int_neg c sg (fun P => Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P))
    (hint.1 (d.n1 • d.wde) (d.et c) (by simp) (hd.et_mem c) (hd.et_ne c))
  set κ := d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo
  refine integral_le_of_ae_le_affine _ _ _ _ _ _ I1 I2 I3 ?_
  filter_upwards [d.norm_at_sg hd h c sg] with z hz
  obtain ⟨hfin0, hcard0, -, -⟩ := hz
  have hfin : (d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)).Finite := hfin0
  have hcard : (d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)).ncard = d.delc c := hcard0
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [Set.ncard_eq_toFinset_card _ hfin] at hcard
  have e : (d.delc c : ℝ) * κ = ∑ P ∈ hfin.toFinset, κ := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  rw [e, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun P _ => ?_
  have hn := hd.nrm_pos c P (hf c).1 (hf c).2
  have hb := d.be_pos hd c P
  have hI := hI2be c P
  rw [Real.log_div hn.ne' hb.ne']
  simp only [κ]
  linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
