import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedAdjoint
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section

namespace GlobalTheory.DiscreteSeriesUnitary

def unitaryModule {p q : ℕ} {T : GrpData p q} (D : DSRep T) : UGKMod p q where
  M := D.HK
  ip := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => inner ℂ (D.ι x) (D.ι y))
    (fun x y z => by simp only [map_add, inner_add_left])
    (fun c x y => by simp only [map_smul, inner_smul_left, smul_eq_mul])
    (fun x y z => by simp only [map_add, inner_add_right])
    (fun c x y => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply])
  herm x y := inner_conj_symm (D.ι y) (D.ι x)
  pos x hx := by
    have h : D.ι x ≠ 0 := fun h => hx (D.ι_inj (h.trans (map_zero D.ι).symm))
    exact re_inner_self_pos (𝕜 := ℂ).2 h
  adj Z x y := GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint p q T D.U D.HK D.ι D.der Z x y

theorem exists_unitary : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T),
    ∃ M : UGKMod p q, M.M = D.HK :=
  fun _ _ _ D => ⟨unitaryModule D, rfl⟩

end GlobalTheory.DiscreteSeriesUnitary

end
