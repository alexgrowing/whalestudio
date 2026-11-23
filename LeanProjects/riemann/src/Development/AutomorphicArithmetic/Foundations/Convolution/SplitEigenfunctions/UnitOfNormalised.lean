import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.RevTop
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.NormCentral
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SpanLevel
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MeasEEx
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.AsaiNV
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.CenExOf
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.UMeasEx
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.UnitCharacterOfCentral
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.DatEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.WeilEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.MeasEx

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem unit_of_normalised {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (hfr : Module.finrank ℚ E = 2)
    {P : CuspSub E 2} {ω : HChar ℚ} (hN : GlobalTheory.DiscSpec.IsNormalised P) (hC : CenN P ω) (a : (A ℚ)ˣ) :
    ‖((ω.1 a : ℂˣ) : ℂ)‖ = 1 := by
  have hu : P.IsUnitary := GlobalTheory.SpehPair.isUnitary_of_isNormalised hN
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 P.ne_bot
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := Function.ne_iff.1 fun e => h0 (Subtype.ext e)
  have h1 := hC φ hφ (ideleEmbedding ℚ E a) g
  have h2 := hu.norm_eq hφ (ideleEmbedding ℚ E a) g
  rw [h1, norm_mul, ideleNorm_ideleEmbedding, hfr, map_pow, Units.val_pow_eq_pow_val, norm_pow] at h2
  have h3 : ‖((ω.1 a : ℂˣ) : ℂ)‖ ^ 2 = 1 := (mul_eq_right₀ (norm_ne_zero_iff.2 hg)).1 h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.downN :
    DownN := by
  intro E _ _ _ hfr P hN hC
  obtain ⟨D⟩ := datEx ℚ E hfr
  obtain ⟨W⟩ := weilEx ℚ E D
  obtain ⟨M⟩ := measEx ℚ
  obtain ⟨N⟩ := measEEx E
  obtain ⟨U⟩ := uMeasEx_of
  obtain ⟨ω, hω⟩ := cenEx_of E hfr P hC
  have hnv := asaiNV E D M U P ω W.η hC hω (unit_of_normalised hfr hN hω) W.quad
  have hper : ∃ φ ∈ P.V, ∃ h : G1 E, (UPer D M fun x => φ.1 (x * gl h)) ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hnv (perU_of E D W M N P U ω hN hω hno)
  obtain ⟨π, hπ, hJ⟩ := rev_holds E D W M N P hper
  obtain ⟨π', hπ', hI⟩ := toII E D W M N P hN π hπ hJ
  exact finS E D W M N P hN π' hπ' hI
