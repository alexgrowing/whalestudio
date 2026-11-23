import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MeanLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ProdBd
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharSel
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharDown
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionBaseChange

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem aE_dM_eq (z w : (A E)ˣ) : aE z * dM w⁻¹ = gl (mD w) * aE (z * w⁻¹) := by
  refine Units.ext ?_
  have e : (gl (mD w)).val = !![(w : A E), 0; 0, ((w⁻¹ : (A E)ˣ) : A E)] := rfl
  rw [Units.val_mul, Units.val_mul, e, aE_val, aE_val, dM_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_left_comm]

private theorem scal_eq {K : Type} [Field K] [NumberField K] (u : (A K)ˣ) :
    GroundTheory.Automorphic.Reduction.scalarUnits K 2 u = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  refine Units.ext ?_
  ext i j
  rw [GroundTheory.Automorphic.Reduction.scalarUnits_apply, GroundTheory.Automorphic.Reduction.coe_diagUnits]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar]

private theorem norm_central (s : {r : ℝ // 0 < r}) :
    ∃ z : (A E)ˣ, GroundTheory.Automorphic.Reduction.centralSection E 2 s = Matrix.GeneralLinearGroup.scalar (Fin 2) z ∧
      Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleNorm ℚ E z) = GroundTheory.Automorphic.Reduction.centralSection ℚ 2 s := by
  have hd : Module.finrank ℚ E ≠ 0 := Module.finrank_pos.ne'
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : {r : ℝ // 0 < r}, s₀ ^ Module.finrank ℚ E = s := by
    refine ⟨⟨s.1 ^ ((Module.finrank ℚ E : ℝ))⁻¹, Real.rpow_pos_of_pos s.2 _⟩, Subtype.ext ?_⟩
    rw [Positive.val_pow]
    exact Real.rpow_inv_natCast_pow s.2.le hd
  obtain ⟨y, hy⟩ : ∃ y : (A ℚ)ˣ, GroundTheory.Automorphic.Reduction.centralSection ℚ 2 s₀ = Matrix.GeneralLinearGroup.scalar (Fin 2) y :=
    ⟨_, (rfl : _ = GroundTheory.Automorphic.Reduction.scalarUnits ℚ 2 _).trans (scal_eq _)⟩
  refine ⟨ideleEmbedding ℚ E y, ?_, ?_⟩
  · rw [← hs₀, ← UpperTheory.centralSection_baseChange ℚ E 2 s₀, hy]
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar]
  · rw [ideleNorm_ideleEmbedding, map_pow, ← hy, ← map_pow, hs₀]

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.toII :
    ToII := by
  intro E _ _ _ D W M N P hP π hπ ⟨f, hf, ph, hph, φ, hφ, hne⟩
  obtain ⟨Φ, hΦ⟩ := UpperTheory.ConvolutionTheory.R2.smooth ℚ E D W M π f hf ph hph
  have hm : Φ ∈ span W M π := Submodule.subset_span ⟨f, hf, ph, hph, hΦ⟩
  have hBd : Bd fun x => Φ.1 x * φ.1 x := (UpperTheory.ConvolutionTheory.RankTwoDescent.prodBd E D W M N P π Φ hm φ hφ).1
  obtain ⟨-, hcont, hgl, hrat⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.meanLaws E N _ hBd
  let β : (A E)ˣ → ℂ := fun t => mean N fun x => Φ.1 (x * aE t) * φ.1 (x * aE t)
  have hβc : Continuous β := hcont.comp continuous_aE
  have hβi : ∀ (e : Eˣ) t, β (IdeleGroup.diagonal E e * t) = β t := fun e t => by
    obtain ⟨γ, hγ⟩ := exists_ratGL_aE (F := E) e
    have h := hrat γ (aE t)
    simp only [β]
    rw [aE_mul, ← hγ]
    exact h
  have hJ : (J1 D N fun x => lift W M f.1 ph x * φ.1 x) =
      UI fun z => β (z * (Units.map (D.bar : A E →* A E) z)⁻¹) := by
    rw [← hΦ]
    refine congrArg UI (funext fun z => ?_)
    have h := hgl (mD (Units.map (D.bar : A E →* A E) z)) (aE (z * (Units.map (D.bar : A E →* A E) z)⁻¹))
    simp only [β, sZ]
    rw [aE_dM_eq]
    exact h
  obtain ⟨χ, h1, h2, h3⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.charSel E D β hβc hβi (by rw [← hJ]; exact hne)
  obtain ⟨χ₀, hχ₀⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.charDown E D χ h1
  have hdet : ∀ (g : G1 ℚ) (n : (A ℚ)ˣ), chiDet 2 χ₀ (gl g * dM n) = χ₀.1 n := fun g n => by
    have e : chiDet 2 χ₀ (gl g * dM n) = χ₀.1 (Matrix.GeneralLinearGroup.det (gl g * dM n)) := rfl
    rw [e, map_mul, det_gl, det_dM, one_mul]
  have hcs : ∀ s, chiDet 2 χ₀ (GroundTheory.Automorphic.Reduction.centralSection ℚ 2 s) = 1 := fun s => by
    obtain ⟨z, hz, hn⟩ := norm_central (E := E) s
    have hz1 : χ₀.1 (ideleNorm ℚ E z) = 1 := by rw [← hχ₀ z]; exact h2 z ⟨s, hz.symm⟩
    have e : chiDet 2 χ₀ (Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleNorm ℚ E z)) =
        χ₀.1 (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleNorm ℚ E z))) := rfl
    rw [← hn, e, det_scalar, map_pow, hz1, one_pow]
  have hlift : ∀ x, lift W M (TR.mulChi 2 χ₀ f).1 ph x = ((χ₀.1 (nu ℚ x) : ℂˣ) : ℂ) * lift W M f.1 ph x := fun x => by
    simp only [lift]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [TR.mulChi_apply, hdet]
    ring
  refine ⟨π.twist χ₀, ?_, TR.mulChi 2 χ₀ f, ⟨f, hf, rfl⟩, ph, hph, φ, hφ, ?_⟩
  · rintro _ ⟨f₁, hf₁, rfl⟩ s g
    change f₁.1 _ * _ = f₁.1 g * _
    rw [hπ f₁ hf₁ s g, map_mul, hcs, one_mul]
  · have e : (II N fun x => lift W M (TR.mulChi 2 χ₀ f).1 ph x * φ.1 x) =
        UI fun t => ((χ.1 t : ℂˣ) : ℂ) * β t := by
      refine congrArg UI (funext fun t => ?_)
      simp only [mean, β]
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun h => ?_)
      simp only [hlift, nu_mul, nu_gl, nu_aE, one_mul, hχ₀ t, hΦ]
      ring
    rw [e]
    exact h3
