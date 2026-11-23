import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.IdeleNormEmbeddingNegOneReal

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.whittaker_unipotent_translate_of_infinite_component_zero :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ), Continuous φ → (∀ γ g, φ (ratGL E 2 γ * g) = φ g) → ∀ x : A ℚ, x.1 = 0 → ∀ (y : (A ℚ)ˣ) (X : GL (Fin 2) (Cinf E)), Wo D (fun g => φ (g * nu D x)) (em E (aE y) * infGL E 2 X) = ψ (-((y : A ℚ) * x)) * Wo D φ (em E (aE y) * infGL E 2 X) := by
  intro E _ _ _ D φ _ hL x hx y X
  have hfst : (AdeleBaseChange.adeleMap ℚ E x).1 = 0 := by
    obtain ⟨c1, c2⟩ := x
    obtain rfl : c1 = 0 := hx
    exact map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E))
  have h0 : pInf E (D.mkE 0 x) = 0 := by
    have h1 : (D.mkE 0 x).1 = 0 := by
      have e : D.mkE 0 x = AdeleBaseChange.adeleMap ℚ E x * rt D.θ := by
        simp only [Dat.mkE, map_zero, zero_add]
      rw [e]
      change (AdeleBaseChange.adeleMap ℚ E x).1 * _ = 0
      rw [hfst, zero_mul]
    change (infEq E).symm (D.mkE 0 x).1 = 0
    rw [h1]
    exact map_zero _
  have hk : GeneralLinearGroup.map (pInf E) (Xg.nu D x) = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    change pInf E ((!![1, D.mkE 0 x; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j) = (1 : Matrix (Fin 2) (Fin 2) (Cinf E)) i j
    fin_cases i <;> fin_cases j <;> simp [h0]
  have hc : infGL E 2 X * Xg.nu D x = Xg.nu D x * infGL E 2 X := by
    have e := infGL_mul_finGL (Xg.nu D x)
    rw [hk, map_one, one_mul] at e
    rw [← e]
    exact infGL_comm X _
  rw [Nz.Wo_right, mul_assoc, hc, ← mul_assoc, Xg.nu, Nz.em_conj, mul_assoc, Nz.Wo_shift D hL]
  rfl
