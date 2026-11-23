import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.abelian₂

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

def ball1 (r p : ℕ) (η : ℝ) : Set (Upq r p) :=
  {g | ∀ a b : Fin r, ‖((g : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b - (if a = b then 1 else 0)‖ ≤ η}

def ballVol (r p : ℕ) (η : ℝ) : ℝ≥0∞ := haarU r p (ball1 r p η)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def uBall (X : Data E r) (η : ℝ) : Set (RealGrp X) := {g | ∀ τ, g τ ∈ ball1 r X.p0 η}

def VolLe (X : Data E r) (V : ℝ) : Prop :=
  quotInt X (fun _ => 1) ≤ ENNReal.ofReal (Real.exp V) * ballVol r X.p0 1 ^ fdeg E

def Thick (X : DataX E r) (ε : ℝ) (x : Frame X.Ψ r) : Prop :=
  ∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (Data.emb τ.1 v)

def Transv (X : DataX E r) (la : Wt X.Ψ r) (M : ℝ) : Prop :=
  ∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
    ∃ γ ∈ X.Γ, X.χ la γ = 1 ∧
      ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.flowMat v τ ((M : ℂ) * τ.1 b)

def wtAbs {Ψ : Finset (E →+* ℂ)} (la : Wt Ψ r) : ℝ := ∑ τ, ∑ i, |(la τ i : ℝ)|

def shortB (f r d ε : ℝ) : ℝ := max 1 ((2 * f * r) ^ 4 * d ^ 2 / (4 * ε))

def injRad (f r d N ε : ℝ) : ℝ := Real.sqrt (ε / shortB f r d ε) / (8 * r ^ 2 * N)

def zNum (f r L d Om : ℝ) : ℝ := f * r + L + Real.log d + |Om|

def lamConst (C f r L d Om S : ℝ) : ℝ :=
  C * zNum f r L d Om ^ 2 * (1 + Real.log S) * S + C * (f * r * L) ^ 3

end GlobalTheory.CompanionTheory.Ar.abelian₂
