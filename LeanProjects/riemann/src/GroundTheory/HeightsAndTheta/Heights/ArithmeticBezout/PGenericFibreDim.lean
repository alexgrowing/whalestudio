import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsGenericFibreDim
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

namespace GenericFibreDim

def blkEquiv (n : ℕ) : Fin n ≃ (Σ _ : Unit, PBlk n ()) where
  toFun i := ⟨(), i⟩
  invFun x := x.2
  left_inv _ := rfl
  right_inv x := by rcases x with ⟨⟨⟩, i⟩; rfl

def blkRingEquiv (n : ℕ) : MvPolynomial (Fin n) ℤ ≃+* MRing (PBlk n) :=
  (renameEquiv ℤ (blkEquiv n)).toRingEquiv

theorem finIdeal_eq_comap {n : ℕ} (P : Ideal (MRing (PBlk n))) :
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal P = P.comap (blkRingEquiv n) := by
  ext x
  rfl

theorem ringKrullDim_quot_finIdeal {n : ℕ} (P : Ideal (MRing (PBlk n))) :
    ringKrullDim (MvPolynomial (Fin n) ℤ ⧸ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) =
      ringKrullDim (MRing (PBlk n) ⧸ P) := by
  rw [finIdeal_eq_comap]
  refine ringKrullDim_eq_of_ringEquiv
    (Ideal.quotientEquiv (P.comap (blkRingEquiv n)) P (blkRingEquiv n) ?_)
  exact (Ideal.map_comap_of_surjective _ (blkRingEquiv n).surjective P).symm

theorem eq_natCast_of_add_one_eq (d : ℕ) (x : WithBot ℕ∞)
    (hform : x + 1 = ((d : ℕ) : WithBot ℕ∞) + 1) : x = d := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd hform (by simp; rw [← Nat.cast_succ]; exact (WithBot.natCast_ne_bot _).symm)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add]; exact_mod_cast hform
      have h2 : ((⊤ : ℕ∞) + 1 : ℕ∞) = ((d + 1 : ℕ) : ℕ∞) := WithBot.coe_injective h1
      rw [top_add] at h2
      exact ENat.top_ne_natCast _ h2
    | coe y =>
      have h1 : ((y + 1 : ℕ) : WithBot ℕ∞) = ((d + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hform
      have : y = d := by exact_mod_cast (by exact_mod_cast h1 : y + 1 = d + 1) |> Nat.succ_injective
      subst this; rfl

end GenericFibreDim

open GenericFibreDim in

theorem GenericFibreDim.proof : GenericFibreDim.Statement := by
  intro n d P hP
  obtain ⟨-, ⟨hPp, -, -⟩, hhor, hdim⟩ := hP
  set P' := IndefiniteRowSideFullHecke.ArithBezout.finIdeal P with hP'
  have hP'p : P'.IsPrime := by
    rw [hP', finIdeal_eq_comap]
    exact Ideal.comap_isPrime _ _
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Fin n) ℤ) ∈ P' → m = 0 := by
    intro m hm
    rw [hP', finIdeal_eq_comap, Ideal.mem_comap] at hm
    have hm' : (blkRingEquiv n) (C m) = C m := by
      simp [blkRingEquiv]
    rw [hm'] at hm
    have : m ∈ P.comap (C : ℤ →+* MRing (PBlk n)) := hm
    rw [show P.comap (C : ℤ →+* MRing (PBlk n)) = ⊥ from hhor, Ideal.mem_bot] at this
    exact this
  obtain ⟨-, -, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec P' hchar
  have hgen : genericIdeal P = ReciprocityTheory.AnForm.R.extQ P' := rfl
  rw [hP', ringKrullDim_quot_finIdeal, hdim] at hform
  rw [hgen]
  simp only [Fintype.card_unit] at hform
  exact eq_natCast_of_add_one_eq d _ hform

end ObjectsChow

end GroundTheory.Heights₂.Heights
