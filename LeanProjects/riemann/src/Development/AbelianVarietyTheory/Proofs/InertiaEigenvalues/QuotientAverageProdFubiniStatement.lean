import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageProdFubini
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientAverage_prod_fubini : ∀ (G₁ : Type) [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] (G₂ : Type) [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂] (Γ₁ : AddSubgroup G₁) (Γ₂ : AddSubgroup G₂), IsCoLat Γ₁ → IsCoLat Γ₂ → ∀ Φ : G₁ × G₂ → ℂ, Per (Γ₁.prod Γ₂) Φ → avg (Γ₁.prod Γ₂) Φ = avg Γ₁ (fun x => avg Γ₂ (fun y => Φ (x, y))) := by
  first | exact @GlobalTheory.CuspGeneric.avg_prod | exact GlobalTheory.CuspGeneric.avg_prod | (intros; apply GlobalTheory.CuspGeneric.avg_prod <;> assumption)
