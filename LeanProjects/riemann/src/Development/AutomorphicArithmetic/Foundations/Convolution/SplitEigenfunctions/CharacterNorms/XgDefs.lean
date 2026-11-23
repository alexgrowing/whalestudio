import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Xg

def Oh (K : Type) [Field K] [NumberField K] : Set (A K) := {c | c.1 = 0 ∧ ∀ v : H.P K, Valued.v (c.2 v) ≤ 1}

def iota (L : ℕ) : A ℚ := (0, algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (L : ℚ)⁻¹)

variable {E : Type} [Field E] [NumberField E]

def nu (D : Dat ℚ E) (x : A ℚ) : GL (Fin 2) (A E) := nE D ![0, x]

def CongE (M : ℕ) (κ : GL (Fin 2) (A E)) : Prop :=
  ∀ i j, (∃ c ∈ Oh E, κ.val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j = (M : A E) * c) ∧
    ∃ c ∈ Oh E, (κ⁻¹).val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j = (M : A E) * c

end UpperTheory.ConvolutionTheory.RankTwoDescent.Xg

end
