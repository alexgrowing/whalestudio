import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageAddOfPeriodic

open GlobalTheory.CuspGeneric

namespace GlobalTheory.CompanionTheory.CuspGeneric

theorem avg_sub_of_per : ∀ {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    (Γ : AddSubgroup G), IsCoLat Γ → ∀ (Φ Φ' : G → ℂ), Per Γ Φ → Per Γ Φ' →
    avg Γ (fun x => Φ x - Φ' x) = avg Γ Φ - avg Γ Φ' := by
  intro G _ _ _ _ _ _ Γ hΓ Φ Φ' h h'
  have hn : Per Γ (fun x => (-1 : ℂ) * Φ' x) :=
    ⟨continuous_const.mul h'.1, fun γ hγ x => by simp only [h'.2 γ hγ x]⟩
  have key := avg_add_of_per G Γ hΓ Φ (fun x => (-1 : ℂ) * Φ' x) h hn
  have e : (fun x => Φ x - Φ' x) = fun x => Φ x + (-1 : ℂ) * Φ' x := by
    funext x; ring
  rw [e, key, avg_const_mul]
  ring

end GlobalTheory.CompanionTheory.CuspGeneric
