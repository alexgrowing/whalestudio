import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.InertSph

theorem exists_rest_tens_ne_zero : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl F),
    ∀ φ ∈ SB (κ → Fv F v), φ ≠ 0 →
    ∃ r : (κ → AF F) → ℂ, Rest (evFin F v) φ r ∧ tens (evFin F v) φ r ≠ 0 := by
  intro F _ _ κ _ v φ hφ hne
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
  refine ⟨R, hR φ hφ, fun h => ?_⟩
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (x i)) :=
    fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have h1 := (hR φ hφ).1 0 _ hz
  rw [zero_add] at h1
  have e := congrFun h (fun i => GlobalTheory.LatVac.liftV v (x i))
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, h1, Pi.zero_apply] at e
  exact mul_ne_zero hx hR0 e

end GlobalTheory.InertSph
