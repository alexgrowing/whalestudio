import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.CoeffCentral

theorem norm_coeff_central : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (p : ℝ), CoeffLp p π → ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ (v : V) (l : Module.Dual ℂ V), IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l} → ‖l (π z v)‖ = ‖l v‖ := by
  intro k _ _ _ _ N V _ _ π p h z hz v l hl
  borelize (AdGL k N)
  obtain ⟨F, hF, -⟩ := h MeasureTheory.Measure.haar inferInstance v l hl
  have h1 : (QuotientGroup.mk z : AdGL k N) = QuotientGroup.mk 1 := by
    rw [QuotientGroup.mk_one]
    exact (QuotientGroup.eq_one_iff z).2 hz
  have h2 := hF z
  rw [h1, hF 1] at h2
  simpa using h2.symm

end GlobalTheory.CompanionTheory.CoeffCentral
