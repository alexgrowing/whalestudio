import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.IrreducibleCuspidalWeightComponent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.HeckeEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.TensAmp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.PosSymb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.RepsSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.EvExSub
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical InnerProductSpace ComplexOrder

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.famScalar :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2))
          [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ → ∀ κ e κ₂ p₁ p₂ k₀, ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ →
          ∀ (S : Finset (Pl K)) (U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w)), Lev U → ∀ (D : TypeDat K (2 + 2)), IsTy D κ e (levOn S U) →
          ∀ (d : ℕ) (A : Line μ τ₁ τ₂ D d) (𝔞 : Amp μ) (φ : TF K (2 + 2)) (c : ℂ) (β : ℝ → Eu d →L[ℂ] Eu d), 𝔞.U = levOn S U →
          (∀ x, φ x = (levOn S U : Set (FA K (2 + 2))).indicator 1 x) → c ≠ 0 → Rop μ (c • tens 𝔞.a₀ φ) = 𝔞.A → ActsBy μ A (c • tens 𝔞.a₀ φ) β →
          (∃ v g, ∫ y, 𝔞.a₀ y * flat 0 (A.sec v) (g * archP K (2 + 2) y) ∂𝔞.ν ≠ 0) → 0 < d ∧ ∃ x : ℝ, 0 < x ∧ symb β 0 = (x : ℂ) • (1 : Eu d →L[ℂ] Eu d) := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP κ e κ₂ p₁ p₂ k₀ hL S U hLev D hD d A 𝔞 φ c β hU hφ hc hR hA hne
  obtain ⟨v₀, g₀, hI⟩ := hne
  have hsec : ∀ v, IsSec τ₁ τ₂ (A.sec v) ∧ D.Fix (A.sec v) := fun v => (A.onto _).1 ⟨v, rfl⟩
  have hflat0 : ∀ x, flat 0 (0 : G1 K (2 + 2) → ℂ) x = 0 := fun x => by simp [flat]
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · exfalso
      apply hI
      rw [show v₀ = 0 from Subsingleton.elim _ _, map_zero]
      simp only [hflat0, mul_zero, integral_zero]
    · exact h
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨h0, h1, -⟩ := UpperTheory.ConvolutionTheory.evEx K (2 + 2) (by norm_num) μ 𝔞
  have hpos := (posSymb A.J 𝔞.A β hA.1 (hR ▸ hA.2.1) h0 h1).1
  have hcomm : ∀ h M, HeckeAt A (levOn S U) h M → Commute M (symb β 0 : Eu d →ₗ[ℂ] Eu d) := by
    have hA' : ActsBy μ A (tens (c • 𝔞.a₀) φ) β := by
      rw [((UpperTheory.ConvolutionTheory.Tf.tensApply K (2 + 2) (by norm_num) 𝔞.a₀ φ).2.2.2.2 c).1]
      exact hA
    exact (heckeEx K μ μ₂ τ₁ τ₂ hP κ e hL.idem S U hLev D hD d A).2.2 _ φ β hφ hA'
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue (symb β 0 : Eu d →ₗ[ℂ] Eu d)
  have hE : Module.End.eigenspace (symb β 0 : Eu d →ₗ[ℂ] Eu d) l = ⊤ := by
    refine (irrW K μ μ₂ τ₁ τ₂ hP κ e κ₂ p₁ p₂ k₀ hL S U hLev D hD d A _ fun w _ g M hM v hv => ?_).resolve_left hl
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have h := LinearMap.congr_fun (hcomm _ M hM).eq v
    simp only [Module.End.mul_apply] at h
    rw [← h, hv, map_smul]
  have hT : ∀ v, symb β 0 v = l • v := fun v =>
    Module.End.mem_eigenspace_iff.1 (hE ▸ Submodule.mem_top : v ∈ Module.End.eigenspace (symb β 0 : Eu d →ₗ[ℂ] Eu d) l)
  have hl0 : 0 ≤ l := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Eu d)
    have hp := (ContinuousLinearMap.nonneg_iff_isPositive _).1 hpos
    have h2 := hp.inner_nonneg_right v
    rw [hT, inner_smul_right, inner_self_eq_norm_sq_to_K] at h2
    have hn : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
    have h3 : 0 ≤ l * ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      simpa using h2
    obtain ⟨a, b⟩ := Complex.nonneg_iff.1 h3
    rw [Complex.re_mul_ofReal] at a
    rw [Complex.im_mul_ofReal] at b
    refine Complex.nonneg_iff.2 ⟨le_of_mul_le_mul_right (by simpa using a) hn, ?_⟩
    exact ((mul_eq_zero.1 (by simpa using b.symm)).resolve_right hn.ne').symm
  have hlne : l ≠ 0 := by
    rintro rfl
    obtain ⟨⟨c', hc', hint, -⟩, -⟩ := tensAmp K (2 + 2) (by norm_num) μ 𝔞 φ (fun x => by rw [hφ, hU])
    have hH : Continuous fun x : G1 K (2 + 2) => Complex.exp ((0 + 2) * (HP 2 2 x : ℂ)) :=
      Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hpSpec.2.2.2.1))
    have hΘ : Continuous (flat 0 (A.sec v₀)) := hH.mul (hsec v₀).1.cont
    have hfix : FixF 𝔞.U (flat 0 (A.sec v₀)) := by
      refine (((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.secTr μ₂ τ₁ τ₂ κ e hL.idem).2.1 _ (hsec v₀).1.cont).2 𝔞.U 𝔞.le).2 ?_
      rw [hU]
      exact ((hD.fix _ (hsec v₀).1.cont).1 (hsec v₀).2).2
    have e1 := hA.2.2 0 v₀ g₀
    rw [hT, zero_smul, map_zero, hflat0] at e1
    simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, mul_assoc] at e1
    rw [integral_const_mul, hint _ hΘ hfix g₀] at e1
    exact mul_ne_zero hc (mul_ne_zero (Complex.ofReal_ne_zero.2 hc'.ne') hI) e1
  obtain ⟨a, b⟩ := Complex.nonneg_iff.1 hl0
  have hre : l = ((l.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← b])
  refine ⟨hd, l.re, lt_of_le_of_ne a fun h => hlne (by rw [hre, ← h]; simp), ?_⟩
  ext1 v
  rw [hT, ← hre]
  simp
