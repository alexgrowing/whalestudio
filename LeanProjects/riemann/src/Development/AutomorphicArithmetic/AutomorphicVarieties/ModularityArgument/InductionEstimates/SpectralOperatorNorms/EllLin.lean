import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.BloIn
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CuspUmg
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsContRep

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem memLp_out {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]
    {v : L2 μ} {φ : G1 K n → ℂ} (hc : Continuous φ) (hr : Reps μ v φ) :
    MemLp (fun m : RightCosetSpace (Gam K n) => φ (Quotient.out m)) 2 (quotientMeasure (Gam K n) μ) := by
  have hinv : ∀ γ ∈ Gam K n, ∀ y, φ (γ * y) = φ y := fun γ hγ => by
    have h1 : (fun y => φ (γ * y)) =ᵐ[μ] φ := by
      filter_upwards [hr, (measurePreserving_mul_left μ γ).quasiMeasurePreserving.ae hr] with y a b
      rw [← a, ← b]
      congr 1
      exact Quotient.sound ⟨⟨γ, hγ⟩, rfl⟩
    exact congrFun (((hc.comp (continuous_const_mul γ)).ae_eq_iff_eq μ hc).1 h1)
  have h2 := IsContRep.ae_eq_quotFun (μ := μ) (φ := v) (F := φ) ⟨hc, hinv, hr⟩
  have h3 : (fun m : RightCosetSpace (Gam K n) => φ (Quotient.out m)) = quotFun φ hinv := by
    funext m
    conv_rhs => rw [← Quotient.out_eq m]
    rfl
  rw [h3]
  exact (Lp.memLp v).ae_eq h2

private theorem int_pair {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)} (b : BW.Blo S 2)
    {τ : Submodule ℂ (L2 (BW.mu1 E 2))} {m B} (hb : BloIn b τ m B) {v : L2 (BW.mu1 E 2)} {φ : G1 E 2 → ℂ} (hc : Continuous φ)
    (hr : Reps (BW.mu1 E 2) v φ) :
    Integrable (fun x : RightCosetSpace (Gam E 2) => φ (Quotient.out x) *
      starRingEnd ℂ (b.f.1 ((Quotient.out x : G1 E 2) : GlobalTheory.CuspRep.GA E 2))) (quotientMeasure (Gam E 2) (BW.mu1 E 2)) := by
  obtain ⟨w, -, hw⟩ := hb.mem
  have hf : Continuous b.f.1 := ((BW.umgOps E 2).2 b.f (BW.cuspUmg E 2 b.f b.cusp).1).1
  exact (memLp_out hc hr).integrable_mul (memLp_out (hf.comp continuous_subtype_val) hw).star

private theorem zt_zero (K : Type) [Field K] [NumberField K] : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.zt K 0 = 1 := by
  have : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext Real.exp_zero
  rw [UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.zt, this, map_one]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.ellLin {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {μ : Measure (normOneGL E (2 + 2))}
    [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : Fam 𝔢) (b b' : BW.Blo 𝔢.S 2) (hb : BloIn b 𝔵.τ₂ 𝔵.m₂ 𝔵.B₂)
    (hb' : BloIn b' 𝔵.τ₁ 𝔵.m₁ 𝔵.B₁) (k : G1 E (2 + 2)) :
    ∃ ℓ : Eu 𝔵.d' →L[ℂ] ℂ, ∀ v, ℓ v = ell b b' k (𝔵.A'.sec v) := by
  set Q := quotientMeasure (Gam E 2) (BW.mu1 E 2)
  let F : Eu 𝔵.d' → RightCosetSpace (Gam E 2) → RightCosetSpace (Gam E 2) → ℂ := fun v m₁ m₂ =>
    𝔵.A'.sec v (lv (Quotient.out m₁) (Quotient.out m₂) 0 * k) *
      starRingEnd ℂ (b.f.1 ((Quotient.out m₁ : G1 E 2) : GlobalTheory.CuspRep.GA E 2)) *
      starRingEnd ℂ (b'.f.1 ((Quotient.out m₂ : G1 E 2) : GlobalTheory.CuspRep.GA E 2))
  have key : ∀ v, (∀ m₁, Integrable (F v m₁) Q) ∧ Integrable (fun m₁ => ∫ m₂, F v m₁ m₂ ∂Q) Q := fun v => by
    obtain ⟨d, φ, ψ, hφ, hψ, h⟩ := (((𝔵.A'.onto _).1 ⟨v, rfl⟩).1).levi k
    have e : ∀ m₁ m₂, F v m₁ m₂ = ∑ i, (φ i (Quotient.out m₁) *
        starRingEnd ℂ (b.f.1 ((Quotient.out m₁ : G1 E 2) : GlobalTheory.CuspRep.GA E 2))) * (ψ i (Quotient.out m₂) *
        starRingEnd ℂ (b'.f.1 ((Quotient.out m₂ : G1 E 2) : GlobalTheory.CuspRep.GA E 2))) := fun m₁ m₂ => by
      simp only [F]
      rw [h (Quotient.out m₁) (Quotient.out m₂) _ (by
        rw [Subgroup.coe_mul, blkLaws.1, neg_zero, zt_zero, mul_one, mul_one]), Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have i₁ := fun i => int_pair b hb (hφ i).1 (hφ i).2.choose_spec.2
    have i₂ := fun i => int_pair b' hb' (hψ i).1 (hψ i).2.choose_spec.2
    refine ⟨fun m₁ => ?_, ?_⟩
    · rw [funext (e m₁)]
      exact integrable_finset_sum _ fun i _ => (i₂ i).const_mul _
    · simp only [e]
      have : ∀ m₁ : RightCosetSpace (Gam E 2), _ := fun m₁ => integral_finset_sum (μ := Q) Finset.univ fun i _ =>
        (i₂ i).const_mul (φ i (Quotient.out m₁) * starRingEnd ℂ (b.f.1 ((Quotient.out m₁ : G1 E 2) : GlobalTheory.CuspRep.GA E 2)))
      simp only [this, integral_const_mul]
      exact integrable_finset_sum _ fun i _ => (i₁ i).mul_const _
  let l : Eu 𝔵.d' →ₗ[ℂ] ℂ :=
    { toFun := fun v => ∫ m₁, ∫ m₂, F v m₁ m₂ ∂Q ∂Q
      map_add' := fun v w => by
        rw [← integral_add (key v).2 (key w).2]
        refine integral_congr_ae (Eventually.of_forall fun m₁ => ?_)
        simp only
        rw [← integral_add ((key v).1 m₁) ((key w).1 m₁)]
        refine integral_congr_ae (Eventually.of_forall fun m₂ => ?_)
        simp only [F, map_add, Pi.add_apply]
        ring
      map_smul' := fun c v => by
        simp only [F, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, integral_const_mul c] }
  exact ⟨LinearMap.toContinuousLinearMap l, fun v => rfl⟩
