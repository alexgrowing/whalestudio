import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.WhittakerHecke.RatIdeleAbsRealIdeleNatIdeleUnitIdeles
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerFunctionContinuousBoundedEquivariant
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsUnipotentDiagRotationLevelDecomposition
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerDiagTorusMulIwasawaEq
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.twisted_zeta_integral_at_compact_eq_at_rotation :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω χ : HChar ℚ),
        CenN P ω → Unit1 ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (L N : ℕ), ChOk χ L → ∀ φ, admitted D ω φ → Gd D P L N φ → ∀ (s : ℂ), ∀ k ∈ KK ℚ, k ∈ SS N → ∀ t : ℝ, re (k 1 0) = Real.sin t → re (k 1 1) = Real.cos t →
        Yt D χ φ s (gl k) = Yt D χ φ s (rot t) := by
  intro E _ _ _ D P ω χ hC hU hχ L N hL φ hA hG s k hk hS t hs hc
  obtain ⟨b, ζ, κ, hζ, hκ, hdec⟩ := UpperTheory.exists_unipotent_diag_rotation_level_decomposition N hG.pos k hk hS t hs hc
  have hab : ab ζ = 1 := UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles.2.2.1 ζ hζ
  have habm : ∀ y : (A ℚ)ˣ, ab (y * ζ ^ 2) = ab y := by
    intro y
    have h1 : IdeleGroup.ideleModule ℚ ζ = 1 := Subtype.ext hab
    show ((IdeleGroup.ideleModule ℚ (y * ζ ^ 2) : {r : ℝ // 0 < r}) : ℝ) = _
    rw [map_mul, map_pow, h1, one_pow, mul_one]
    rfl
  have hχω : ((ω.1 ζ⁻¹ : ℂˣ) : ℂ) ^ 2 = ((χ.1 ζ : ℂˣ) : ℂ) ^ 2 := by
    have h := hχ ζ
    have h2 : (ω.1 ζ⁻¹) ^ 2 = (χ.1 ζ) ^ 2 := by
      rw [map_inv, inv_pow, inv_eq_iff_mul_eq_one, ← mul_pow, mul_comm]
      exact h
    exact_mod_cast congrArg (fun u : ℂˣ => (u : ℂ)) h2
  let Gf : IdeleGroup ℚ → ℂ := fun y => Wo D φ (em E (aE y * rot t)) * ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1)
  have key : ∀ y : IdeleGroup ℚ, Wo D φ (em E (aE y * gl k)) * ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1) = Gf (y * ζ ^ 2) := by
    intro y
    rw [hdec, UpperTheory.whittaker_diagTorus_mul_iwasawa_eq E D ω φ hA N hG.lev y ζ b (rot t) κ hκ, hχω]
    show _ = Wo D φ (em E (aE (y * ζ ^ 2) * rot t)) * ((χ.1 (y * ζ ^ 2) : ℂˣ) : ℂ) * ((ab (y * ζ ^ 2) : ℝ) : ℂ) ^ (s - 1)
    have hχm : χ.1 (y * ζ ^ 2) = χ.1 y * χ.1 ζ ^ 2 := by rw [map_mul, map_pow]
    rw [habm, hχm]
    push_cast
    ring
  unfold Yt
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  exact integral_mul_right_eq_self Gf (ζ ^ 2)
