import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast

noncomputable section

open Formalism.Per
open scoped Formalism.Per

namespace GlobalTheory.PSer

variable {l : ℕ} [Fact l.Prime]

def sh (x : Fl l) : ℂ_[l] := ((x.untilt : OC l) : ℂ_[l])

def pw (k : ℤ) (x : Fl l) : Fl l := ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ k : RingAut (Fl l)) x

def lam (h j : ℕ) (x : Fl l) : ℂ_[l] := ∑' n : ℤ, (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)

def abelian₂ (h j : ℕ) (y : ℕ → Fl l) : ℂ_[l] := ∑' k : ℕ, (l : ℂ_[l]) ^ k * lam h j (y k)

def gam (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) : ℝ :=
  ⨆ n : ℤ, ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))

end GlobalTheory.PSer

end
