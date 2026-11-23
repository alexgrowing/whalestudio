import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL

noncomputable section

set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.Rd

attribute [local instance] PositivityTheory.Rg.BcB.F.borelF

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private def fac {κ : Pl E → Type} {a b : ℕ} (P : Finset (Pl E)) (L : LM κ a b) (x y : ∀ w : P, κ w) (h : Hf E a b)
    (w : Pl E) : ℂ :=
  L.ent P x y w (atW w h) * if IsSplitAt w then L.t w (atW w (thP E a b h)) else 1

theorem levCof {n : ℕ} (d : LocData E n) (a : ℕ) :
    ∀ᶠ w : Pl E in cofinite, d.lev a w = K2 a (n - a) w ∧ d.lev₂ a w = K2 a (n - a) w := by
  refine Filter.eventually_cofinite.2 ((d.T ∪ d.S₀ ∪ d.Bad).finite_toSet.subset fun w hw => ?_)
  by_contra hc
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hc
  apply hw
  unfold LocData.lev LocData.lev₂
  simp [hc.1.1, hc.1.2, hc.2]

end PositivityTheory.Rg.BcB.F.Rd

end
