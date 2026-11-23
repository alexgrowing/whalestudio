import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.Pst

theorem finiteDimensional_Dst_of_isSst : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type)
    [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V),
    IsSst P ρ → FiniteDimensional ℚ_[l] ↥(Dst P ρ) := by
  intro l _ P K V _ _ _ ρ h
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  by_cases hV : 0 < finrank ℚ_[l] V
  · have hK : 0 < finrank ℚ_[l] ↥(K0 K) := Module.finrank_pos
    have hpos : 0 < finrank ℚ_[l] ↥(Dst P ρ) := by
      unfold IsSst at h
      rw [h]
      exact Nat.mul_pos hK hV
    exact Module.finite_of_finrank_pos hpos
  · have h0 : finrank ℚ_[l] V = 0 := Nat.eq_zero_of_not_pos hV
    haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    haveI : Subsingleton (V ⊗[ℚ_[l]] Bst P) := by
      refine ⟨fun x y => ?_⟩
      have hx : ∀ z : V ⊗[ℚ_[l]] Bst P, z = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul v b => rw [Subsingleton.elim v 0, zero_tmul]
        | add x y hx hy => rw [hx, hy, add_zero]
      rw [hx x, hx y]
    infer_instance

end GlobalTheory.Pst
