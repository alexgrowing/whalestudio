import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NormalRepresentationLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SecondCountableLocal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.FlatSourceStable

theorem om_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) {Φ : Matrix b a k → ℂ} (hΦ : Φ ≠ 0) : om μ g h Φ ≠ 0 := by
  intro h0
  apply hΦ
  have h1 := om_mul μ g⁻¹ g h⁻¹ h Φ
  rw [inv_mul_cancel, inv_mul_cancel, om_one, h0] at h1
  rw [h1]
  funext x
  simp [om]

theorem flat_ne_zero_of_mem_R : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ) (g : GL (n' ⊕ Fin (c + 1 + 1)) k) (h : GL (n ⊕ Fin (c + 1)) k), flat ψ ν μ Φ g h ≠ 0 → ∀ r ∈ R k n' (c + 1 + 1) 1, flat ψ ν μ Φ (r * g) h ≠ 0 := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ψ ν _ μ Φ g h h0 r hr
  obtain ⟨x, u, hu, rfl⟩ := GlobalTheory.RootEx.Radical.exists_of_mem_R hr
  unfold flat at h0 ⊢
  have e : om μ (embX (c + 1 + 1) x * u * g) h Φ =
      om μ (embX (c + 1 + 1) x) 1 (om μ u 1 (om μ g h Φ)) := by
    rw [← om_mul, ← om_mul, one_mul, one_mul]
  rw [e, (GlobalTheory.RootEx.opE_om_embX k n n' (c + 1) 1 le_rfl (by omega) ψ ν μ _).2 x,
    GlobalTheory.RootExSource.opE_om_source k n n' (c + 1) 1 le_rfl (by omega) ψ ν μ _ u hu]
  refine smul_ne_zero ?_ (om_ne_zero μ _ _ (smul_ne_zero (Circle.coe_ne_zero _) h0))
  exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (nabs_pos k _) _).ne'

end GlobalTheory.FlatSourceStable
