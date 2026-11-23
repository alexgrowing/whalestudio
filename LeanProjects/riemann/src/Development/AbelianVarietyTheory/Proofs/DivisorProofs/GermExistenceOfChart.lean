import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An

namespace GlobalTheory.LatJet.An

theorem germEx_of_chart_holLift : Chart → HolLift → GermEx := by
  intro hC hH E _ _ _ I _ 𝔠 φ c y _ _ n T J Y
  obtain ⟨B, _, _, hsm, X, δ, j, q, hpull⟩ := hC (FR E) 𝔠 I n J Y.X'
  obtain ⟨δ'', hδ'', -⟩ := GlobalTheory.RealMult.Obj.IsPullBy.existsUnique_detGen (j : B →+* J.B) hpull δ
  have hmem : Y.δ'.1 ∈ Submodule.span J.B {δ''.1} := by
    rw [δ''.2]; exact Submodule.mem_top
  obtain ⟨e, he⟩ := Submodule.mem_span_singleton.1 hmem
  obtain ⟨U, yy, hU, h0, hhol, hjet⟩ := hH B I n J j
  exact ⟨{
    B := B
    smooth := hsm
    X := X
    δ := δ
    j := j
    q := q
    pull := hpull
    δ'' := δ''
    corr := hδ''
    e := e
    he := he.symm
    U := U
    isOpen := hU
    zero := h0
    y := yy
    hol := hhol
    jet_eq := hjet }⟩

end GlobalTheory.LatJet.An
