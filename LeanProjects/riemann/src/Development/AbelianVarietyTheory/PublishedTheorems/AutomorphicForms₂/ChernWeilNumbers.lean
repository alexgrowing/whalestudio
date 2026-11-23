import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality

noncomputable section

namespace GlobalTheory.Published

open AlgebraicGeometry CategoryTheory MvPolynomial GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

def ChernWeilNumbers : Prop :=
  ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0)
    (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (gr : Root m → Y.Dv),
    Refines E E' φ f → IsGraded E' gr →
      ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H →
        ∀ R : MvPolynomial (ι × ℕ) ℝ, HasChernIntegral E ⊤ H R (Y.interPoly gr (chernRoots m R * fibrePoint m))

end GlobalTheory.Published

end
