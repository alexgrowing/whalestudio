import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexOrder

noncomputable section

def nD (f p q : ℕ) : ℕ := f * (p * q)

def Zof {f p q : ℕ} (v : V (nD f p q)) (k : Fin f) : Matrix (Fin p) (Fin q) ℂ :=
  Matrix.of fun a b => v (finProdFinEquiv (k, finProdFinEquiv (a, b)))

def Dset (f p q : ℕ) : Set (V (nD f p q)) :=
  {v | ∀ k, (1 - Zof v k * (Zof v k)ᴴ).PosDef}

def rh {f p q : ℕ} (v : V (nD f p q)) : ℝ :=
  -∑ k, Real.log (1 - Zof v k * (Zof v k)ᴴ).det.re

def zPart {f p q N' : ℕ} (v : V (nD f p q + N')) : V (nD f p q) :=
  WithLp.toLp 2 fun j => v (Fin.castAdd N' j)

def tPart {f p q N' : ℕ} (v : V (nD f p q + N')) : V N' :=
  WithLp.toLp 2 fun j => v (Fin.natAdd (nD f p q) j)

def OmSet (f p q N' : ℕ) : Set (V (nD f p q + N')) := {v | zPart v ∈ Dset f p q}

def eOm {f p q N' : ℕ} (v : V (nD f p q + N')) : ℝ :=
  rh (zPart v) + Real.log (1 + ‖tPart v‖ ^ 2)

def ExhaustStatement : Prop :=
  ∀ f p q N' : ℕ, ∃ S : EtaleStein (nD f p q + N') (OmSet f p q N'),
    S.z = Subtype.val ∧ S.e = fun y => eOm y.1

def RhGradStatement : Prop :=
  ∀ f p q : ℕ, ∀ v ∈ Dset f p q, ∀ ξ : Fin (nD f p q) → ℂ,
    Complex.normSq (∑ j, wd (nD f p q) j (fun w => ((rh w : ℝ) : ℂ)) v * ξ j) ≤
      ((f * min p q : ℕ) : ℝ) * (leviV (nD f p q) (fun w => ((rh w : ℝ) : ℂ)) v ξ).re

def PolyGrowthStatement : Prop :=
  ∀ (D m : ℕ) (P Q : MvPolynomial (Fin D) ℂ), Q ≠ 0 →
    (∃ C : ℝ, ∀ y : Fin D → ℂ, MvPolynomial.eval y Q ≠ 0 →
      ‖MvPolynomial.eval y P / MvPolynomial.eval y Q‖ ≤ C * (1 + ∑ i, ‖y i‖) ^ m) →
    ∃ R : MvPolynomial (Fin D) ℂ, R.totalDegree ≤ m ∧ P = R * Q

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
