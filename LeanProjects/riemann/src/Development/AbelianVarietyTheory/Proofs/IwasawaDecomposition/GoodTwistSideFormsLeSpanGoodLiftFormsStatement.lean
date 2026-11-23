import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistSideFormsLeSpanGoodLiftForms
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCentralGroupAlgebraIdempotentUniversal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.V0T_le_span_image_goodL : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool),
    1 ≤ j → j ≤ D.R.m → EIdem D → ∀ (Φ : S.WL j →+ FmT D T S i j b),
    (∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x) →
    (∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x)) →
    (∀ x : S.WL j, Φ ((∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g) x) =
      eGT D T S In.rho In.chi i j b (Φ x)) →
    (∀ w : ↥(WKr D S j), Φ (w : S.WL j) = (1 : KT D T i b) ⊗ₜ[S.Ks] w) →
    V0T D T S In.rho In.chi In.θ i j b ≤
      Submodule.span (FractionRing (T.O i)) (Φ '' (goodL D S In.θ j : Set (S.WL j))) := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.goodTwistSideForms_le_span_goodLiftForms | exact GlobalTheory.HeightCounting.FormsStep.goodTwistSideForms_le_span_goodLiftForms | (intros; apply GlobalTheory.HeightCounting.FormsStep.goodTwistSideForms_le_span_goodLiftForms <;> assumption)
