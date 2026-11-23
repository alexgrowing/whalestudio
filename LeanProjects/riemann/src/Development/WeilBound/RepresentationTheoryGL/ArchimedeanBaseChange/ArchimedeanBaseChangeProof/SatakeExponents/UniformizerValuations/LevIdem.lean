import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.FrameBound

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

def LevIdem : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (d : LocData E n) (a : ℕ),
  a ≤ n → IsSection S → d.Ok → (↑d.P : Set (Pl E)) ⊆ S →
  (IsOpen (lev₁ S d a : Set (GL (Fin a) (Af E))) ∧ IsCompact (lev₁ S d a : Set (GL (Fin a) (Af E)))) ∧
  (IsOpen (lev₂ S d a : Set (GL (Fin (n - a)) (Af E))) ∧ IsCompact (lev₂ S d a : Set (GL (Fin (n - a)) (Af E)))) ∧
  (((lev₁ S d a).prod (lev₂ S d a) : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a))) = levSet S d a ∧
  ∀ (ν : Measure (Hf E a (n - a))), ν.IsHaarMeasure → ∃ cK : ℂ,
    cK * (ν.real (((lev₁ S d a).prod (lev₂ S d a) : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a))) : ℂ) = 1 ∧
    ∀ (x y : ∀ w : d.P, d.kap w) (h : Hf E a (n - a)),
      ((ν.real ((Kf E a).prod (Kf E (n - a)) : Subgroup (Hf E a (n - a))) : ℝ) : ℂ)⁻¹ *
          finFn S ((d.eL a).ent d.P x y) (d.eL a).t h =
        if x = y ∧ h ∈ ((lev₁ S d a).prod (lev₂ S d a) : Subgroup (Hf E a (n - a))) then cK else 0

end PositivityTheory.Rg.BcB.F

end
