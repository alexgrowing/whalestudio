import Mathlib
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceBoundOddRamifiedOfCharts

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PlaceTop
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie

def ramLoss (D : D7) {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {j : ℕ} (w : WeightFamilies.Wt D j) : ℝ :=
  ∑ p ∈ D.host.condN.primeFactors, ((vLa la (p : K) : ℤ) : ℝ) * D.host.vdH p * (DF w : ℝ) / 2

def ThBoundSt : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (_hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D),
    Oriented T EX → ∀ (w : WeightFamilies.Wt D j) (g : T.R j), g ∈ T.th j w →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la),
      ((-(ramLoss D la w + ((vLa la ((nnW (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ)) : ℝ) : EReal) ≤
        vAtV y g

def ShortBoundSt : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (_hs : LawsSh T) (j : ℕ) (_hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL)
    (EX : ErrX D), Oriented T EX → ∀ (w : WeightFamilies.Wt D j) (g : T.R j), g ∈ T.sh j w →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la),
      ((-(ramLoss D la w + ((vLa la ((nnW (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ) +
          ((vLa la ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) : ℤ) : ℝ) * (D.R.f * D.R.r * w.n : ℕ) +
          ((vLa la (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) : ℤ) : ℝ) * (DF w + D.R.f * D.R.r * w.n : ℕ)) : ℝ) : EReal) ≤ vAtV y g

def ScaledLatticesInSupLattices : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (_hs : LawsSh T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL)
    (EX : ErrX D), Oriented T EX → ∀ p : ℕ, (∀ n, (T.dδ j n).pd = p) →
    ∀ (ka wL wF : WeightFamilies.Wt D j) (T₀ nP : ℕ), IsF' ka wL wF T₀ nP →
      H2 (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF T₀) ka wL wF ∧
      ∀ n : GlobalTheory.RunIn.SecNorm (recB h.toLawsCore),
        H2 (GlobalTheory.RunIn.recPlusN h j hj n)
          (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF T₀)) ka wL wF

end GlobalTheory.PlaceTop
