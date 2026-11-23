import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.lie_action_preserves_fixed_at_place :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (w : H.P E) (f : Sm E 2) (X : Lie E 2), H.Fix w f.1 → H.Fix w (lie E 2 X f).1 := by
  intro E _ _ _ w f X hf g k hk
  have h1 : rt E 2 (finGL E 2 (locGL E 2 w k)) f = f :=
    Subtype.ext (funext fun x => hf x k hk)
  have h2 : lie E 2 X (rt E 2 (finGL E 2 (locGL E 2 w k)) f) =
      rt E 2 (finGL E 2 (locGL E 2 w k)) (lie E 2 X f) :=
    LinearMap.congr_fun (lie_rt_fin X (locGL E 2 w k)) f
  rw [h1] at h2
  exact (congrArg (fun u : Sm E 2 => u.1 g) h2).symm
