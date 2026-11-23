import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.LocGL

theorem isLSeg_of_isL_singleton : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsL {Δ} π → IsLSeg Δ π := by
  intro k _ _ _ _ Δ N V _ _ π h
  obtain ⟨h', x, hd, ⟨Δ', ⟨hm, -⟩, hL⟩, hc⟩ := h
  have hcard : h' = 1 := by
    have := congrArg Multiset.card hm
    simpa using this
  subst hcard
  have hΔ : Δ' 0 = Δ := by
    have hmem : Δ' 0 ∈ Finset.univ.val.map Δ' := Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)
    rw [hm] at hmem
    simpa using hmem
  have hL0 : IsLSeg Δ (x 0).rep := hΔ ▸ hL 0
  obtain ⟨y, rfl⟩ : ∃ y, x = fun _ => y := ⟨x 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hN : y.1 = N := by simpa using hd
  subst hN
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one y hd
  obtain ⟨φ⟩ := hc.unique ((isCosocle_self y.2.rep.irr).of_equiv (.refl _) ψ)
  exact hL0.of_equiv φ

end GlobalTheory.CompanionTheory.LocGL
