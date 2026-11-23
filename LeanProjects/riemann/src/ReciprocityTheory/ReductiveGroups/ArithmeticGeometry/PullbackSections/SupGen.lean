import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

def FockDerivSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (N n : ℕ), 1 ≤ N →
    ∀ s ∈ X.Sec 1 1, ∀ S : ℝ, (∀ v, X.ptN2 1 s v ≤ S) →
    ∀ (a : Fin n → Vsp X.dim) (ι : Type) (P : MvPolynomial ι ℂ) (u : ι → Fin n → Vsp X.dim),
      (∀ l, ∑ b, ‖u l b‖ ^ 2 ≤ 1) →
      ‖polyDeriv P u (X.U (N ^ 2) a (s0 X ((N : ℂ) • LinearMap.id) s)) 0‖ ≤
        (∑ m ∈ P.support, ‖P.coeff m‖) * (N : ℝ) ^ P.totalDegree *
          (Real.pi * Real.exp 1 * P.totalDegree) ^ ((P.totalDegree : ℝ) / 2) * S ^ ((n : ℝ) / 2)

def SupSecSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E), ∀ s ∈ X.Sec 1 1, ∀ v,
    X.ptN2 1 s v ≤ 2 * (1 + 4 * Real.sqrt (2 * Fintype.card (Idx X.dim)) / (Real.sqrt Real.pi * X.la1)) ^
      (2 * Fintype.card (Idx X.dim)) * X.l2 1 s

def La1AtSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r),
    x ∈ X.dom → ∀ A : TorusAt X x, X.firstMinimumSq x ≤ A.T.la1 ^ 2

def SupArithSt : Prop :=
  ∀ (L a ℓ S v p1 la lsq : ℝ) (d n g f r : ℕ), 2 ≤ L → 0 < ℓ → Real.log ℓ ≤ 2 * L * a → 0 < S → S ≤ 2 * v →
    v ≤ p1 * (Real.pi * Real.exp 1 * d) ^ ((d : ℝ) / 2) *
      (2 * (1 + 4 * Real.sqrt (2 * g) / (Real.sqrt Real.pi * la)) ^ (2 * g)) ^ ((n : ℝ) / 2) →
    Real.log p1 ≤ 140 * r * L * a + 4 * f * r * n * L → (d : ℝ) ≤ a → Real.log (1 + a) ≤ 2 * L → g ≤ f * r → 1 ≤ f → 1 ≤ r →
    r ≤ n → Real.log f ≤ 2 * L → Real.log n ≤ L → 0 ≤ la → 0 < lsq → lsq ≤ la ^ 2 →
    Real.log (1 / lsq) ≤ 44 * L →
      Real.log (ℓ * S) ≤ (140 * r + 4) * L * a + 67 * f * r * n * L

end ReciprocityTheory.ChartRestriction.G.PullbackSections
