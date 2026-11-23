import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

open Polynomial
namespace GlobalTheory.Published

def GreenSeriesSt : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∃ τ : (ZMod g)[X] → GlobalTheory.BadShare.GG g N → ℂ, 0 < N → GlobalTheory.BadShare.IsSeries τ

end GlobalTheory.Published
