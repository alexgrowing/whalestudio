import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilOne
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.RealLift.OneParam GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.RealK GlobalTheory.ThK.StepK

noncomputable section

namespace GlobalTheory.ThK.StepK.Low

variable {R S : ℕ}

def upIx : Ix R S → Ix (R + 1) (S + 1) := Sum.map Fin.succ Fin.succ

variable (R S) in

def lowInc : Matrix (Ix (R + 1) (S + 1)) (Ix R S) ℂ := Matrix.of fun a b => if a = upIx b then 1 else 0

theorem upIx_injective : Function.Injective (upIx (R := R) (S := S)) :=
  Sum.map_injective.2 ⟨Fin.succ_injective _, Fin.succ_injective _⟩

@[simp] theorem upIx_ne_inl (b : Ix R S) : upIx b ≠ .inl 0 := by
  rcases b with b | b <;> simp [upIx]

@[simp] theorem upIx_ne_inr (b : Ix R S) : upIx b ≠ .inr 0 := by
  rcases b with b | b <;> simp [upIx]

@[simp] theorem inl_ne_upIx (b : Ix R S) : Sum.inl 0 ≠ upIx b := (upIx_ne_inl b).symm

@[simp] theorem inr_ne_upIx (b : Ix R S) : Sum.inr 0 ≠ upIx b := (upIx_ne_inr b).symm

@[simp] theorem upIx_inj {a b : Ix R S} : upIx a = upIx b ↔ a = b := upIx_injective.eq_iff

end GlobalTheory.ThK.StepK.Low

end
