import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilOne
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.RealLift.OneParam GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.RealK GlobalTheory.ThK.StepK

noncomputable section

namespace GlobalTheory.ThK.StepK.VanishZero

def kcSub (p q : ℕ) : Submodule ℂ (Mat p q) where
  carrier := {Z | IsKC Z}
  add_mem' := fun {X Y} hX hY a b h => by
    simp only [Set.mem_setOf_eq] at hX hY
    rw [Matrix.add_apply, hX a b h, hY a b h, add_zero]
  zero_mem' := fun a b _ => rfl
  smul_mem' := fun c X hX a b h => by
    simp only [Set.mem_setOf_eq] at hX
    rw [Matrix.smul_apply, hX a b h, smul_zero]

end GlobalTheory.ThK.StepK.VanishZero
