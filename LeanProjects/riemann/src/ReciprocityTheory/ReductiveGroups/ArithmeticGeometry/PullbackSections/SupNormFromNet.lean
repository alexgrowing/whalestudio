import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LogSupSumLeOfNonvanishingDetLimit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def netNorm (U : Unf Xo c σ r) (la : ∀ k, Wt (U.X k).Ψ r) (NN : Finset (FPt U.X)) (P : FDSec U.X) : ℝ :=
  Real.sqrt ((NN.card : ℝ)⁻¹ * ∑ p ∈ NN, ((U.X p.1).pnorm (la p.1) (P p.1) p.2) ^ 2)

def NnOf (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (NN : Finset (FPt U.X)) (f : Rul Xo c) : ℝ :=
  dmet n (Module.finrank ℚ E / 2) r * netNorm U (laU U a n) NN (rdU U f)

def IsNet (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (NN : Finset (FPt U.X)) : Prop :=
  NN.Nonempty ∧ ∀ P ∈ holSub U.X (laU U a n),
    supN U.X (laU U a n) P ≤ 4 * Real.sqrt NN.card * netNorm U (laU U a n) NN P

def NetExistsSt : Prop :=
  ∃ Cn : ℝ, ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j)
    (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → SupBoundPageRows D large₂ ka →
    ∃ NN : Finset (FPt (T.U j σ).X), IsNet (T.U j σ) (wtA ka) ka.n NN ∧
      Real.log (16 * NN.card) ≤ Cn * Zb D large₂ ^ 3

def AlgInjAtSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ),
    GoodEmb T.Q.c σ → ∀ (m : ℕ) (f : Fin m → T.C j ka),
      LinearIndependent T.Q.c.F f → LinearIndependent ℂ (fun i => rdU (T.U j σ) (f i : T.R j))

def NnLawsSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ),
    GoodEmb T.Q.c σ → ∀ NN : Finset (FPt (T.U j σ).X), IsNet (T.U j σ) (wtA ka) ka.n NN →
    (∀ f ∈ T.C j ka, 0 ≤ NnOf (T.U j σ) (wtA ka) ka.n NN f) ∧
    (∀ f ∈ T.C j ka, NnOf (T.U j σ) (wtA ka) ka.n NN f = 0 → f = 0) ∧
    (∀ (x : T.Q.c.F), ∀ f ∈ T.C j ka,
      NnOf (T.U j σ) (wtA ka) ka.n NN (x • f) = ‖σ x‖ * NnOf (T.U j σ) (wtA ka) ka.n NN f) ∧
    (∀ f ∈ T.C j ka, ∀ g ∈ T.C j ka,
      NnOf (T.U j σ) (wtA ka) ka.n NN (f + g) ≤
        NnOf (T.U j σ) (wtA ka) ka.n NN f + NnOf (T.U j σ) (wtA ka) ka.n NN g) ∧
    (∀ f ∈ T.C j ka, NnOf (T.U j σ) (wtA ka) ka.n NN f ≤ supNU (T.U j σ) (wtA ka) ka.n f)

def SupNormFromNet : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ),
    GoodEmb T.Q.c σ → ∀ NN : Finset (FPt (T.U j σ).X), IsNet (T.U j σ) (wtA ka) ka.n NN →
    ∀ f ∈ T.C j ka, supNU (T.U j σ) (wtA ka) ka.n f ^ 2 ≤ 16 * NN.card * NnOf (T.U j σ) (wtA ka) ka.n NN f ^ 2

def LogDFromNetSt : Prop :=
  AlgInjAtSt →
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ),
    GoodEmb T.Q.c σ → ∀ NN : Finset (FPt (T.U j σ).X), IsNet (T.U j σ) (wtA ka) ka.n NN →
    Module.finrank T.Q.c.F (T.C j ka) ≤ NN.card

def HermFromNetSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j)
    (NN : ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → Finset (FPt (T.U j σ).X)),
    (∀ σ (hσ : GoodEmb T.Q.c σ), IsNet (T.U j σ) (wtA ka) ka.n (NN σ hσ)) →
    ∃ (dH : ℕ) (Hm : Formalism.MainNotions.Gaps.SizeBoundsAlt.Herm
        (fun σ (f : T.C j ka) => NnOf (T.U j (goodOf T.Q.c σ)) (wtA ka) ka.n
          (NN (goodOf T.Q.c σ) (goodEmb_goodOf T.Q.c σ)) (f : T.R j)) dH), Hm.Conj

end ReciprocityTheory.ChartRestriction.G.PullbackSections
