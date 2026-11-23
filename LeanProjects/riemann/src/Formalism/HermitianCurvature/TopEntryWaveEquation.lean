import Formalism.HermitianCurvature.TopDensNonnegOfKappa
import Formalism.HermitianCurvature.ActualZetaSmooth

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

def TopEntryWaveEquation : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)), IsPlace P z z' π π' →
    ∀ (X : ActualOps P.k P.r z z' π π') (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')),
      multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)) → multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g)) →
      ∀ Y, mkP Wv' Wv * X.QQ Y 0 0 * mkP Wv Wv' =
        (Matrix.conjTranspose (Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s) * X.QQ Y *
          Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s : Matrix (Fin 2) (Fin 2) (Pr (RadSp P.k P.r z z' π π'))) 0 0

def WaveQQTopOfZeta : Prop := NF.ActualZetaSmooth → TopEntryWaveEquation → WaveQQTop

def TopTwistDensOfZeta : Prop :=
  NF.ActualZetaSmooth →
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')),
    IsData P z z' π π' X μ L st l0 → TopTwistDens S P z z' π π' L st l0 K

def HerClassesOfPartsD : Prop :=
  NormalFormActual → KappaFibrePos → NF.ActualZetaSmooth → HerAnalyticCAll → HerClasses

end Formalism.FourierDecayAlt.P5
