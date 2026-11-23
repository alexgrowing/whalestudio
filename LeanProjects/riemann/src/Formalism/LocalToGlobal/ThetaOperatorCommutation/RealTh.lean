import Mathlib
import Formalism.PeriodIntegrals.JointBlockShapes.JointShape
import ReciprocityTheory.ThetaSummability.RealCoinvariants.CoinvSubLeComap

noncomputable section

open MvPolynomial FockH1Action ReciprocityTheory.ThetaSummability.Real

namespace ReciprocityTheory.ChartRestriction.G.ThK.Real

variable {p q r s : ℕ}

def chiTr (c : ℂ) (Z : Mat p q) : ℂ := c * Z.trace

def KCMat (p q : ℕ) : Type := {Z : Mat p q // IsKC Z}

def act1 (p q r s : ℕ) (Z : Mat p q) : Module.End ℂ (Pol p q r s) := fockAct1 p q r s Z

def polChi (p q r s : ℕ) (c : ℂ) : Submodule ℂ (Pol p q r s) :=
  jointEig (fun Z : KCMat p q => fockAct1 p q r s Z.1) (fun Z => chiTr c Z.1)

def jHarm (p q r s : ℕ) : Submodule ℂ (Pol p q r s) := Submodule.span ℂ (Jset p q r s)

abbrev ThC (p q r s : ℕ) (c : ℂ) := Coinv (act1 p q r s) (chiTr c)

def thMkC (p q r s : ℕ) (c : ℂ) : Pol p q r s →ₗ[ℂ] ThC p q r s c :=
  (coinvSub (act1 p q r s) (chiTr c)).mkQ

end ReciprocityTheory.ChartRestriction.G.ThK.Real
