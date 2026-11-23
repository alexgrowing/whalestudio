import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KJStdInt

theorem carries_std_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n) → (∀ i j, k.1 i j ∈ Formalism.L2.Herm.intAf F E) ∧ ∀ i j, (k⁻¹).1 i j ∈ Formalism.L2.Herm.intAf F E := by
  intro F E _ _ _ _ _ n k hk
  letI : StarRing E := starRingOfComm
  have hm : ∀ z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F,
      z ∈ Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E n) ↔ ∀ i, z i ∈ Formalism.L2.Herm.intAf F E :=
    fun z => Formalism.L2.Col.mem_latS_std z
  have hs : ∀ j : Fin n, (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E n) := by
    intro j
    refine (hm _).2 fun i => ?_
    by_cases h : i = j
    · subst h
      rw [Pi.single_eq_same]
      exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne h]
      exact Subring.zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have h1 : (k⁻¹).1 *ᵥ (k.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) ∈
        Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E n) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact hs j
    have h2 := (hm _).1 ((hk _).2 h1) i
    rwa [Matrix.mulVec_single_one] at h2
  · have h2 := (hm _).1 ((hk _).1 (hs j)) i
    rwa [Matrix.mulVec_single_one] at h2

end GlobalTheory.KJStdInt
