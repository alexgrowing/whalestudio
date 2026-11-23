import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

noncomputable section

namespace UpperTheory.ConvolutionTheory.GM.TE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def Cnd (S : Finset (Pl F)) (q : Pl F) (κ : Finset (Pl E)) : Set (AdelicGLn.FiniteAdelicGL E n) :=
  {x | ∀ w : Pl E, w ∉ κ → w.under (𝓞 F) ∉ S → w.under (𝓞 F) ≠ q →
    cf w x ∈ GLnLocal.integralGL (w.adicCompletion E) n}

open Classical in

def rF (S : Finset (Pl F)) {q : Pl F} (w₀ : PlacesOver E q) (ψ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ)
    (κ : Finset (Pl E)) (x : AdelicGLn.FiniteAdelicGL E n) : ℂ :=
  (∏ v ∈ S, ψ v (mapGL n (atFin v) (finEmb E n x))) *
    (∏ᶠ w : PlacesOver E q, if w = w₀ then 1 else (iwCoset w.1 (0 : Fin n → ℤ)).indicator 1 (cf w.1 x)) *
    (Cnd S q κ).indicator 1 x

end UpperTheory.ConvolutionTheory.GM.TE
