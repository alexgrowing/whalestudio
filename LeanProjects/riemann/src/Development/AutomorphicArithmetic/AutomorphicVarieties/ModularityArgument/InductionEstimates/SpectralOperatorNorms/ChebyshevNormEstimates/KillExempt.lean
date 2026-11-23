import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatDatum
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.KillCore
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Langlands
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RhoLe
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.KillComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.BloVSummand
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.Exempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.MapUnivAdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.CtZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.CompZero

open MeasureTheory NumberField MvPolynomial GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.BW PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
open scoped InnerProductSpace

private theorem qz {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (A B C D : H →L[ℂ] H) {X Y : H →L[ℂ] H} (h1 : A ∘L B = X)
    (h2 : A ∘L C = Y) (h3 : A - X = D) (h4 : D - Y = 0) : A ∘L (1 - B - C) = 0 := by
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_sub, h1, h2, ← h4, ← h3]
  rfl

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.killExempt :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KillExempt := by
  intro K _ _ _ μ _ θ 𝔢 𝔵 η hη
  obtain ⟨ρ, Cb, hCb, hcore⟩ := killCore (n := 2 + 2) (by norm_num) 𝔢.toAmp η hη
  obtain ⟨B, hB⟩ := far K (2 + 2) Cb hCb
  obtain ⟨D₀, hfin, hD₀⟩ := KX.near2 K 𝔢.S (2 + 2) ρ B
  let D : Set (Dat 𝔢.S (2 + 2)) := {d ∈ D₀ | 2 ≤ d.len ∧ ¬ d.On 𝔵.Λ 𝔵.t}
  have hD : D.Finite := hfin.subset (Set.sep_subset _ _)
  choose b hb using fun d : D => KX.datOn K 𝔢.S (2 + 2) d.1 d.2.2.1
  refine ⟨D, hD.fintype, b, fun d => ⟨_, _, (hb d _ _).2 ⟨0, rfl, fun _ _ => rfl⟩⟩, fun d h => d.2.2.2 ((hb d _ _).1 h),
    fun ev hev hP χ hχ hχ0 _ F G hF hFb hG => ?_⟩
  obtain ⟨sa, idem, hker⟩ := 𝔵.isP
  have hc : ∀ y, Pc μ y ∈ cuspidalL2 μ := fun y => Submodule.starProjection_apply_mem _ y
  have saC : IsSelfAdjoint (Pc μ) := isSelfAdjoint_starProjection _
  have sy : ∀ a b, ⟪a, Pc μ b⟫_ℂ = ⟪Pc μ a, b⟫_ℂ := fun a b => (saC.isSymmetric a b).symm
  have PPc : 𝔵.P ∘L Pc μ = 0 := by
    ext1 y
    show 𝔵.P (Pc μ y) = 0
    refine (hker _).2 ⟨fun u => ?_, fun v => ?_⟩
    · rw [sy, (ctZero K μ _ _ _ 𝔵.pair _ _ _ 𝔵.A 𝔵.A' u).1, inner_zero_left]
    · rw [sy,
        (ctZero K μ _ _ _ ⟨𝔵.pair.irr₂, 𝔵.pair.irr₁, 𝔵.pair.orth.symm⟩ _ _ _ 𝔵.A' 𝔵.A v).1, inner_zero_left]
  have PcP : Pc μ ∘L 𝔵.P = 0 := by
    have := congrArg star (show 𝔵.P * Pc μ = 0 from PPc)
    rwa [star_mul, sa.star_eq, saC.star_eq, star_zero] at this
  have PcPc : Pc μ ∘L Pc μ = Pc μ := (Submodule.isIdempotentElem_starProjection _).eq
  refine hcore ev hev 𝔵.P (1 - Pc μ - 𝔵.P) hP ?_ ?_ χ hχ hχ0 F G hF hG fun y φ w hy hw hφ hs hkw hsw hsum => ?_
  · exact qz _ _ _ _ PcPc PcP (sub_self _) (sub_zero _)
  · exact qz _ _ _ _ PPc idem (sub_zero _) (sub_self _)
  refine (langlands K 𝔢.S _ ρ w hw.umg hkw hsw).2 fun k d hd hlen => ?_
  by_cases hon : d.On 𝔵.Λ 𝔵.t
  · have hA : 𝔵.P (Rop μ 𝔢.a y) = 0 := by
      have := DFunLike.congr_fun (hP (C (X none)) (by simp)) y
      rw [hev.amp] at this
      simp only [ContinuousLinearMap.comp_apply, hy, map_zero] at this
      rw [𝔢.a_op]; exact this.symm
    obtain ⟨o1, o2⟩ := (hker _).1 hA
    rw [← 𝔢.a_op] at hw
    obtain ⟨b₁, b₂, rfl, h | h⟩ := KX.exempt K μ θ 𝔢 𝔵 d hlen hon
    · exact KX.compZero μ _ _ 𝔵.D 𝔵.A 𝔵.pair.irr₁ 𝔵.pair.irr₂ 𝔢.a 𝔵.a_hecke y w hw o1 b₁ b₂ h.1 h.2 k
    · exact KX.compZero μ _ _ 𝔵.D 𝔵.A' 𝔵.pair.irr₂ 𝔵.pair.irr₁ 𝔢.a 𝔵.a_hecke y w hw o2 b₁ b₂ h.1 h.2 k
  refine killComp K 𝔢.S _ Cb φ w F G hCb hφ hs hw.umg hF.2 hG hsum k d ?_
  by_cases hfar : ∃ τ i, B < ‖d.lam τ i‖
  · exact Or.inr fun ψ hψ hSψ => hB 𝔢.S d ψ hψ hSψ hfar
  · push Not at hfar
    obtain ⟨d', hd', hl, hk⟩ := hD₀ d hd hfar
    exact Or.inl fun z => hFb ⟨d', hd', hl ▸ hlen, fun h => hon ((hk _ _).1 h)⟩ _ _
      ((hb _ _ _).2 ((hk _ _).2 ⟨z, rfl, fun _ _ => rfl⟩))
