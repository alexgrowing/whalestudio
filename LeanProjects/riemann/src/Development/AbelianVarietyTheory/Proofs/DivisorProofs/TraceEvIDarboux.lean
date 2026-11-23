import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

namespace GlobalTheory.ArchSch

theorem trace_evI_darboux : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module (AF F) V]
    {B : V → V → AF F} (d : Darboux B κ) (w w' : V),
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (B w w')) =
      trP F κ (arch F (d.e w).1) (arch F (d.e w').2) - trP F κ (arch F (d.e w').1) (arch F (d.e w).2) := by
  intro F _ _ κ _ V _ _ B d w w'
  let f : AF F →+* mixedEmbedding.mixedSpace F :=
    { toFun := fun a => evI F a
      map_one' := by simp only [evI]; exact map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)
      map_mul' := fun a b => by simp only [evI]; exact map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
      map_zero' := by simp only [evI]; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
      map_add' := fun a b => by simp only [evI]; exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1 }
  have hf : ∀ a, f a = evI F a := fun _ => rfl
  have hsum : ∀ (x y : κ → AF F), evI F (x ⬝ᵥ y) = ∑ i, arch F x i * arch F y i := fun x y => by
    rw [← hf, dotProduct, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_mul f _ _
  rw [d.form, ← hf, map_sub, hf, hf, hsum, hsum, map_sub, mixedTracePairing_apply, mixedTracePairing_apply]

end GlobalTheory.ArchSch
