import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.FinHeis

namespace GlobalTheory.FinHeis

theorem heisFin_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ),
    Continuous ψ → ∀ (a b : κ → Af F), ∀ g ∈ SB (κ → Af F), heisFin F ψ a b g ∈ SB (κ → Af F) := by
  intro F _ _ κ _ ψ hψ a b g hg
  have h := GlobalTheory.HeisSchA.finS_mem ψ hψ hg b a 0
  have e : heisFin F ψ a b g = GlobalTheory.HeisSchA.finS ψ g b a 0 := by
    funext z
    simp only [heisFin, GlobalTheory.HeisSchA.finS, add_zero, GlobalTheory.HeisSchA.finChar_apply]
    rfl
  rw [e]; exact h

end GlobalTheory.FinHeis
