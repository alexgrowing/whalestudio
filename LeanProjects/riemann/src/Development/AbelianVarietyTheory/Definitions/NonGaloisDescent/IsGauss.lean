import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable (l : ℕ) [Fact l.Prime]

def gA (ρ : ℝ) (a : Formalism.Per.Ainf l) : ℝ :=
  ⨆ n : ℕ, ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n

def IsGauss (ρ : ℝ) (N : Formalism.Per.Acris l → ℝ) : Prop :=
  (∀ x, 0 ≤ N x ∧ N x ≤ 1) ∧ (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ (∀ x, N (-x) = N x) ∧
    (∀ x y, N (x * y) = N x * N y) ∧
    ∀ a : Formalism.Per.Ainf l, N (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) = gA l ρ a

open Classical in

def gC (ρ : ℝ) (x : Formalism.Per.Acris l) : ℝ :=
  if h : ∃ N, IsGauss l ρ N then Classical.choose h x else 0

def vr (r : ℝ) (x : Formalism.Per.Acris l) : ℝ := -Real.logb l (gC l ((l : ℝ) ^ (-r)) x)

def zc : ℤ_[l] →+* Formalism.Per.Acris l := (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)).comp (Formalism.Per.zA l)

def tc (y : Formalism.Per.Fl l) : Formalism.Per.Acris l := algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.tm y)

abbrev φc : Formalism.Per.Acris l →+* Formalism.Per.Acris l := GlobalTheory.MemLoc.phiA l

end GlobalTheory.PMon.Gauss

end
