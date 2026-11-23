import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.IntegralMemFd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.PiLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LineVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.TypeOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MaximalCompactUniqueArchFiniteDecomposition
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalSpanMaximalCompactTranslatesOfF
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCuspidalSectionFromLeviAverage
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LeviInducedSectionFixedByArchIdempotentAndLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsLevelAndKTypeVectorForLeviInduction

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.lineEx :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ →
      ∀ (μ : Measure U4) (e : ι → U4 → ℂ) n q n' q' (x : ι → U4), Haar4 μ → ExtP μ e n q n' q' x →
      (∀ i, ∃ v ∈ τ₁, C.Pi μ₂ i (n i) (q i) v ≠ 0) → (∀ i, ∃ v ∈ τ₂, C.Pi μ₂ i (n' i) (q' i) v ≠ 0) →
      ∀ S : Finset (Pl K), SphOff μ₂ τ₁ S → SphOff μ₂ τ₂ S →
        ∃ (U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w)) (f : G1 K (2 + 2) → ℂ), Lev U ∧ f ≠ 0 ∧ IsSec τ₁ τ₂ f ∧ FixA (C.κ₄ μ) (C.e e) f ∧ FixF (levOn S U) f := by
  intro K _ _ _ ι _ C μ₂ _ τ₁ τ₂ hP μ e n q n' q' x hμ hE h₁ h₂ S hS₁ hS₂
  obtain ⟨U₁, φ₁, hU₁, hφ₁, hR₁, hB₁, hA₁, hF₁⟩ := vecEx K ι C μ₂ τ₁ hP.irr₁ n q h₁ S hS₁
  obtain ⟨U₂, φ₂, hU₂, hφ₂, hR₂, hB₂, hA₂, hF₂⟩ := vecEx K ι C μ₂ τ₂ hP.irr₂ n' q' h₂ S hS₂
  obtain ⟨-, -, hId, -⟩ := piLaws K ι C μ₂
  have hfd : ∀ (p : archCompact K 2 → ℂ) (V : ∀ w : Pl K, Subgroup (Gw 2 w)) (φ : G1 K 2 → ℂ), IdemA C.κ₂ p → Lev V → Continuous φ → FixA C.κ₂ p φ →
      FixF (levOn S V) φ → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KG K 2 => fun m => φ (m * k))) := by
    intro p V φ hp hV hc ha hf
    obtain ⟨hco, hle⟩ := (IwahoriBlocks.levLaws (K := K) 2 S).1 V hV
    obtain ⟨D, hD, -⟩ := typeOf K 2 C.κ₂ p hp (levOn S V) hle hco.2
    exact UpperTheory.finiteDimensional_span_maximalCompact_translates_of_fix D φ hc ((hD.fix φ hc).2 ⟨ha, hf⟩)
  obtain ⟨U, ρ, Ψ, c, hU, hρ, hρi, hΨ, hN, hΨA, hΨF, hc, hval⟩ := UpperTheory.exists_level_and_KTypeVector_for_leviInduction K ι C μ e n q n' q' x hμ hE S U₁ U₂ hU₁ hU₂
  obtain ⟨f, hfc, hfb, hfu, hfr, hfs, hform⟩ := UpperTheory.exists_cuspidal_section_from_levi_average μ₂ τ₁ τ₂ hP.irr₁ hP.irr₂ ρ hρ hρi Ψ hΨ hN φ₁ φ₂ hR₁.cont hR₂.cont hB₁ hB₂ hR₁.rep hR₂.rep
    (hfd _ U₁ φ₁ (hId n q) hU₁ hR₁.cont hA₁ hF₁) (hfd _ U₂ φ₂ (hId n' q') hU₂ hR₂.cont hA₂ hF₂)
  obtain ⟨hfixA, hfixF⟩ := UpperTheory.leviInducedSection_fixed_by_archIdempotent_and_level ρ hρ Ψ hΨ φ₁ φ₂ hR₁.cont hR₂.cont hB₁ hB₂ f hform
  obtain ⟨hIdem, -⟩ := lineVal K ι C μ₂ τ₁ τ₂ hP μ e n q n' q' x hμ hE
  obtain ⟨hco, hle⟩ := (IwahoriBlocks.levLaws (K := K) (2 + 2) S).1 U hU
  have fA := hfixA _ _ hIdem hΨA
  have fF := hfixF _ hle hΨF
  obtain ⟨D, hD, -⟩ := typeOf K (2 + 2) (C.κ₄ μ) (C.e e) hIdem (levOn S U) hle hco.2
  have hDf : D.Fix f := (hD.fix f hfc).2 ⟨fA, fF⟩
  refine ⟨U, f, hU, ?_, (secCrit μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂ f hDf).2 ⟨hfc, hfb, hfu, hfr, hfs⟩, fA, fF⟩
  intro h0
  obtain ⟨m₁, hm₁⟩ := Function.ne_iff.1 hφ₁
  obtain ⟨m₂, hm₂⟩ := Function.ne_iff.1 hφ₂
  obtain ⟨-, -, -, -, -, -, hkA, -⟩ := UpperTheory.maximalCompact_unique_arch_finite_decomposition (K := K) (2 + 2)
  have hv := hform 0 m₁ m₂ 0 _ (hkA ((C.Φ (2 + 2)).symm x))
  rw [hval φ₁ φ₂ hR₁.cont hR₂.cont hA₁ hA₂ hF₁ hF₂ m₁ m₂, h0] at hv
  have : (c : ℂ) * φ₁ m₁ * φ₂ m₂ ≠ 0 := mul_ne_zero (mul_ne_zero (by exact_mod_cast hc.ne') hm₁) hm₂
  exact this hv.symm
