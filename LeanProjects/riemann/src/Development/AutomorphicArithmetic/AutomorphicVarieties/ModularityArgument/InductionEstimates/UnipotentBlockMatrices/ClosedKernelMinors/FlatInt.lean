import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TChiKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ThBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BfFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.DenseCc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsContRep

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

variable {K : Type} [Field K] [NumberField K]

private theorem th_int (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (a : CC K (2 + 2)) (F : G1 K (2 + 2) → ℂ)
    (hc : Continuous F) (hi : ∀ γ ∈ PK K, ∀ g, F (γ * g) = F g) (hb : InBand F) (x : G1 K (2 + 2)) :
    ∫ g, a g * th F (x * g) ∂μ = th (fun y => ∫ g, a g * F (y * g) ∂μ) x := by
  have hC : IsCompact ((x * ·) '' tsupport (a : G1 K (2 + 2) → ℂ)) :=
    a.hasCompactSupport.isCompact.image (continuous_const_mul x)
  have hS := (thBasic μ F hc hi hb).1 _ hC
  have h0 : ∀ q : Cos K, q ∉ hS.toFinset → ∀ g, a g * F ((q.out : G1 K (2 + 2)) * x * g) = 0 := by
    intro q hq g
    by_cases hg : g ∈ tsupport (a : G1 K (2 + 2) → ℂ)
    · by_contra hne
      refine hq (hS.mem_toFinset.2 ⟨x * g, ⟨g, hg, rfl⟩, fun h => hne ?_⟩)
      rw [mul_assoc, h, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hg, zero_mul]
  have h1 : ∀ g, a g * th F (x * g) = ∑ q ∈ hS.toFinset, a g * F ((q.out : G1 K (2 + 2)) * x * g) := by
    intro g
    rw [th, mul_finsum, finsum_eq_sum_of_support_subset (s := hS.toFinset)]
    · simp only [mul_assoc]
    · intro q hq
      by_contra hn
      exact hq (by simpa only [mul_assoc] using h0 q hn g)
  simp only [h1]
  rw [integral_finset_sum, th, finsum_eq_sum_of_support_subset (s := hS.toFinset)]
  · intro q hq
    by_contra hn
    exact hq (by simp only [h0 q hn, integral_zero])
  · intro q _
    exact (a.continuous.mul (hc.comp (continuous_const_mul _))).integrable_of_hasCompactSupport
      a.hasCompactSupport.mul_right

private theorem rep_sum {μ : Measure (G1 K (2 + 2))} [μ.IsHaarMeasure] {ι : Type} (s : Finset ι) (φ : ι → L2 μ)
    (F : ι → G1 K (2 + 2) → ℂ) (h : ∀ i, IsContRep μ (φ i) (F i)) : IsContRep μ (∑ i ∈ s, φ i) (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isContRep_zero
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (h i).add ih

private theorem exp_cast (t : ℝ) : Complex.exp ((((2 + 2 : ℕ) : ℝ) / 2 * t : ℝ) : ℂ) = Complex.exp (2 * (t : ℂ)) := by
  congr 1
  push_cast
  ring

private theorem specW [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure]
    {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} (hP : Pair μ₂ τ₁ τ₂) {D : TypeDat K (2 + 2)} {d : ℕ} (A : Line μ τ₁ τ₂ D d)
    (w : ℝ → Eu d) (hw : Continuous w) (hwc : HasCompactSupport w) (u : L (Eu d)) (hu : ∀ᵐ x : ℝ, u x = w x) :
    IsContRep μ (A.J u) (th fun y => Complex.exp (2 * (HH y : ℂ)) * A.sec (w (HH y)) y) := by
  let e := EuclideanSpace.basisFun (Fin d) ℂ
  have hc : ∀ i, Continuous fun x => w x i := fun i => by fun_prop
  have hcc : ∀ i, HasCompactSupport fun x => w x i := fun i =>
    hwc.mono fun x hx h0 => hx (by simp only [h0]; rfl)
  have hsum : ∀ x, w x = ∑ i, w x i • e i := fun x => (e.sum_repr (w x)).symm
  choose U hU using fun i => (denseCc d).2.1 (fun x => w x i) (e i) (hc i) (hcc i)
  have huU : u = ∑ i, U i := by
    refine Lp.ext ?_
    filter_upwards [hu, MeasureTheory.Lp.coeFn_finsetSum Finset.univ U, ae_all_iff.2 hU] with x h1 h2 h3
    rw [h1, h2, hsum x]
    simp only [Finset.sum_apply, h3]
  have hB : ∀ i, PFun (bf (fun x => w x i) (A.sec (e i))) ∧ InBand (bf (fun x => w x i) (A.sec (e i))) := fun i => by
    have h := (A.onto (A.sec (e i))).1 ⟨_, rfl⟩
    have h' := bfFun _ _ (secFun μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂ _ h.1 h.2) (hc i) (hcc i)
    exact ⟨h'.1, h'.2.1⟩
  have hT := fun i => thBasic μ _ (hB i).1.cont (hB i).1.rat (hB i).2
  have hR := rep_sum Finset.univ (fun i => A.J (U i)) (fun i => th (bf (fun x => w x i) (A.sec (e i))))
    fun i => ⟨(hT i).2.1, (hT i).2.2.1, A.spec _ _ _ (hc i) (hcc i) (hU i)⟩
  rw [huU, map_sum]
  convert hR using 1
  funext x
  simp only [Finset.sum_apply, th]
  rw [← finsum_sum_comm]
  · refine finsum_congr fun q => ?_
    rw [hsum (HH _), map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, bf, exp_cast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  · intro i _
    exact ((hT i).1 {x} isCompact_singleton).subset fun q hq => ⟨x, rfl, hq⟩

private theorem rep_ext {μ : Measure (G1 K (2 + 2))} [μ.IsHaarMeasure] {φ ψ : L2 μ} {F : G1 K (2 + 2) → ℂ}
    (h : IsContRep μ φ F) (h' : IsContRep μ ψ F) : φ = ψ :=
  Lp.ext (h.ae_eq_quotFun.trans h'.ae_eq_quotFun.symm)

private theorem w_cc {d : ℕ} (κ : ℝ → Eu d →L[ℂ] Eu d) (hk : Ker κ) (β : ℝ → ℂ) (v : Eu d) (hβ : Continuous β)
    (hβc : HasCompactSupport β) :
    Continuous (fun x => ∫ s, β (x + s) • κ s v) ∧ HasCompactSupport (fun x => ∫ s, β (x + s) • κ s v) := by
  have hconv : (fun x => ∫ s, β (x + s) • κ s v) =
      MeasureTheory.convolution β (fun s => κ (-s) v) (ContinuousLinearMap.lsmul ℝ ℂ) volume := by
    funext x
    rw [MeasureTheory.convolution]
    refine Eq.trans ?_ (integral_add_left_eq_self _ x)
    simp
  have hκc : Continuous fun s => κ (-s) v := (hk.1.comp continuous_neg).clm_apply continuous_const
  have hκcc : HasCompactSupport fun s => κ (-s) v :=
    (hk.2.comp_homeomorph (Homeomorph.neg ℝ)).mono fun s hs h0 => hs (by
      have : κ (-s) = 0 := h0
      simp [this])
  rw [hconv]
  exact ⟨hκcc.continuous_convolution_right _ hβ.locallyIntegrable hκc, hβc.convolution _ hκcc⟩

private theorem bf_int (μ : Measure (G1 K (2 + 2))) (a : CC K (2 + 2)) (β : ℝ → ℂ) (f : G1 K (2 + 2) → ℂ) (y : G1 K (2 + 2)) :
    ∫ g, a g * bf β f (y * g) ∂μ = Complex.exp (2 * (HH y : ℂ)) * tChi μ a (fun s => β (HH y + s)) f y := by
  rw [tChi, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [bf, exp_cast, add_sub_cancel, HH]
  generalize HP 2 2 (y * g) = s
  generalize HP 2 2 y = t
  rw [show Complex.exp (2 * (s : ℂ)) = Complex.exp (2 * (t : ℂ)) * Complex.exp (2 * ((s - t : ℝ) : ℂ)) by
    rw [← Complex.exp_add]; congr 1; push_cast; ring]
  ring

private theorem flat_int (μ : Measure (G1 K (2 + 2))) (a : CC K (2 + 2)) (z : ℂ) (f : G1 K (2 + 2) → ℂ) (x : G1 K (2 + 2)) :
    ∫ g, a g * flat z f (x * g) ∂μ = flat z (tChi μ a (fun s => Complex.exp (z * s)) f) x := by
  simp only [flat]
  rw [tChi, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [HH]
  generalize HP 2 2 (x * g) = s
  generalize HP 2 2 x = t
  rw [show Complex.exp ((z + 2) * (s : ℂ)) = Complex.exp ((z + 2) * (t : ℂ)) *
    (Complex.exp (z * ((s - t : ℝ) : ℂ)) * Complex.exp (2 * ((s - t : ℝ) : ℂ))) by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring]
  ring

private theorem rop_rep (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (a : CC K (2 + 2)) (F : G1 K (2 + 2) → ℂ)
    (hc : Continuous F) (hi : ∀ γ ∈ PK K, ∀ g, F (γ * g) = F g) (hb : InBand F) (φ : L2 μ) (hφ : Reps μ φ (th F)) :
    IsContRep μ (Rop μ a φ) (th fun y => ∫ g, a g * F (y * g) ∂μ) := by
  have r2 : IsContRep μ (Rop μ a φ) (rconv (Gam K (2 + 2)) μ a φ) := isContRep_rconv μ a φ
  have hEq : rconv (Gam K (2 + 2)) μ a φ = th fun y => ∫ g, a g * F (y * g) ∂μ := by
    funext x
    rw [← th_int μ a F hc hi hb, rconv, integral_congr_ae (g := fun y => a (x⁻¹ * y) * th F y) (hφ.mono fun y hy => by
      simp only [hy]), ← integral_mul_left_eq_self _ x]
    simp only [inv_mul_cancel_left]
  rwa [hEq] at r2

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.convR :
    ConvRC := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP D d d' A A' a ha
  obtain ⟨κ, hk, hκ⟩ := tChiKer μ μ₂ τ₁ τ₂ D A hP.irr₁ hP.irr₂ a ha
  refine ⟨κ, hk, ?_, ?_⟩
  · have key : ∀ u, Rop μ a (A.J u) = A.J (UpperTheory.V.Z.IntegralApplyAeEq.conv κ u) := by
      have hE : (Rop μ a) ∘L A.J.toContinuousLinearMap = A.J.toContinuousLinearMap ∘L UpperTheory.V.Z.IntegralApplyAeEq.conv κ := by
        refine ContinuousLinearMap.ext_on (denseCc d).1 ?_
        rintro u ⟨β, v, hβ, hβc, hu⟩
        show Rop μ a (A.J u) = A.J (UpperTheory.V.Z.IntegralApplyAeEq.conv κ u)
        obtain ⟨hw, hwc⟩ := w_cc κ hk β v hβ hβc
        have hcu : ∀ᵐ x : ℝ, UpperTheory.V.Z.IntegralApplyAeEq.conv κ u x = ∫ s, β (x + s) • κ s v := by
          filter_upwards [(UpperTheory.V.Z.IntegralApplyAeEq.convSpec κ hk u).1] with x hx
          rw [hx]
          refine integral_congr_ae ?_
          filter_upwards [(measurePreserving_add_left volume x).quasiMeasurePreserving.ae hu] with t ht
          rw [ht, map_smul]
        have r1 := specW μ hP A _ hw hwc _ hcu
        have h := (A.onto (A.sec v)).1 ⟨_, rfl⟩
        have h' := bfFun _ _ (secFun μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂ _ h.1 h.2) hβ hβc
        have r2 := rop_rep μ a _ h'.1.cont h'.1.rat h'.2.1 _ (A.spec β v u hβ hβc hu)
        have e2 : ∀ y : G1 K (2 + 2), ∫ g, a g * bf β (A.sec v) (y * g) ∂μ =
            Complex.exp (2 * (HH y : ℂ)) * A.sec (∫ s, β (HH y + s) • κ s v) y := fun y => by
          rw [bf_int, hκ (fun s => β (HH y + s)) v (hβ.comp (continuous_const_add _))]
        simp only [e2] at r2
        exact rep_ext r2 r1
      exact fun u => DFunLike.congr_fun hE u
    intro u v hv
    have e : UpperTheory.V.Z.IntegralApplyAeEq.conv κ u = v := by
      refine Lp.ext ?_
      filter_upwards [(UpperTheory.V.Z.IntegralApplyAeEq.convSpec κ hk u).1, hv] with x h1 h2
      rw [h1, h2]
    rw [key, e]
  · intro z v x
    have hz : Continuous fun s : ℝ => Complex.exp (z * s) := by fun_prop
    have e3 : symb κ z v = ∫ s : ℝ, Complex.exp (z * s) • κ s v := by
      exact ContinuousLinearMap.integral_apply ((hz.smul hk.1).integrable_of_hasCompactSupport hk.2.smul_left) v
    rw [e3, flat_int, hκ _ v hz]
