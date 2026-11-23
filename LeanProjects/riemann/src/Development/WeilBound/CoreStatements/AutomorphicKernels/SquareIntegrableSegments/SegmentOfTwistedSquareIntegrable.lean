import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TempProdUsedOf
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CohomologicalCsdTemperedOfUsed
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.Development
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace PositivityTheory.PfEss.H13

theorem isLSeg_of_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Δ : Segment k} {x y : IrrGL k} (hxy : x = y) (h : IsLSeg Δ x.rep) : IsLSeg Δ y.rep := by
  subst hxy
  exact h

theorem segment_of_twisted_square_integrable (hU : PositivityTheory.Zltwo.EssSqIntUsed) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (δ : IrrGL k), 1 ≤ δ.1 →
      (∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsSqIntCoeff (δ.tw χ hχ).rep) → ∃ Δ : Segment k, IsLSeg Δ δ.rep := by
  intro k _ _ _ _ _ δ hδ ⟨χ, hχ, hs⟩
  obtain ⟨Δ', hΔ'⟩ := hU k (δ.tw χ hχ) hδ hs
  refine ⟨Δ'.tw χ⁻¹ hχ.inv, ?_⟩
  exact isLSeg_of_eq (IrrGL.tw_tw_inv δ χ hχ)
    ((hΔ'.tw χ⁻¹ hχ.inv).of_equiv ((δ.tw χ hχ).twEquiv χ⁻¹ hχ.inv))

theorem square_integrable_of_segment_twist
    (h2 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (y : IrrGL k),
      ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy (y.tw χ hχ) t c → ‖c‖ = 1)
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSegJacquet k → ∀ (δ : IrrGL k), (∃ Δ : Segment k, IsLSeg Δ δ.rep) →
      ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsSqIntCoeff (δ.tw χ hχ).rep := by
  intro k _ _ _ _ hJ δ ⟨Δ, hΔ⟩
  obtain ⟨χ, hχ, hc⟩ := h2 k δ
  exact ⟨χ, hχ, Zls.FreeSingleHomotopyEquivDiscreteChains.centredSegSqInt k hA hF hJ (Δ.tw χ hχ) (δ.tw χ hχ)
    ((hΔ.tw χ hχ).of_equiv (δ.twEquiv χ hχ)) hc⟩

end PositivityTheory.PfEss.H13

end
