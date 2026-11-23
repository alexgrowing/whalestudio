import Development.WeilBound.CoreStatements.PublishedTheorems.LanglandsClassification.LanglandsClassification2
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace PositivityTheory.Lit1

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_isLSeg {Δ : Segment k} {x y : IrrGL k} (hx : IsLSeg Δ x.rep) (hy : IsLSeg Δ y.rep) : x = y := by
  obtain ⟨n, a⟩ := x
  obtain ⟨m, b⟩ := y
  have hn : n = m := hx.deg_eq.symm.trans hy.deg_eq
  subst hn
  obtain ⟨e⟩ := hx.unique hy
  have hab : a = b := Quotient.out_equiv_out.mp ⟨e.symm⟩
  rw [hab]

theorem eq_of_isCosocle {h : ℕ} {z : Fin h → IrrGL k} {x y : IrrGL k} {hd : ∑ a, (z a).1 = x.1} {hd' : ∑ a, (z a).1 = y.1}
    (hx : IsCosocle x.rep (prodIrr z hd)) (hy : IsCosocle y.rep (prodIrr z hd')) : x = y := by
  obtain ⟨n, x⟩ := x
  obtain ⟨m, y⟩ := y
  obtain rfl : n = m := hd.symm.trans hd'
  exact (IrrGL.of_rep ⟨n, x⟩).symm.trans ((IrrGL.of_eq_of.2 (hy.unique hx)).trans (IrrGL.of_rep ⟨n, y⟩))

variable {Lseg : Segment k → IrrGL k} {L : Multiset (Segment k) → IrrGL k} (h1 : ∀ Δ, IsLSeg Δ (Lseg Δ).rep)
  (h3 : ∀ (𝔪 : Multiset (Segment k)) (h : ℕ) (Δ : Fin h → Segment k), IsOrderedForm Δ 𝔪 →
    ∃ hd : ∑ a, (Lseg (Δ a)).1 = (L 𝔪).1, IsCosocle (L 𝔪).rep (prodIrr (fun a => Lseg (Δ a)) hd))

include h1 h3 in
theorem cosocle_of_lFactors {𝔪 : Multiset (Segment k)} {h : ℕ} {x : Fin h → IrrGL k} (hx : LFactors 𝔪 x) :
    ∃ hd : ∑ a, (x a).1 = (L 𝔪).1, IsCosocle (L 𝔪).rep (prodIrr x hd) := by
  obtain ⟨Δ, ho, hΔ⟩ := hx
  obtain rfl : x = fun a => Lseg (Δ a) := funext fun a => eq_of_isLSeg (hΔ a) (h1 _)
  exact h3 𝔪 h Δ ho

include h1 h3 in
theorem eq_of_isL {𝔪 : Multiset (Segment k)} {x : IrrGL k} (hx : IsL 𝔪 x.rep) : x = L 𝔪 := by
  obtain ⟨h, z, hd, hz, hc⟩ := hx
  obtain ⟨hd', hc'⟩ := cosocle_of_lFactors h1 h3 hz
  exact eq_of_isCosocle hc hc'

end

end PositivityTheory.Lit1

end
