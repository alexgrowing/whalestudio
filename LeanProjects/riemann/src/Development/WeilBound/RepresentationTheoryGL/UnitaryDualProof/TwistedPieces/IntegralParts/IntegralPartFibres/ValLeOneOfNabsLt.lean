import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.ContinuousOnZpart
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.ContinuousLinearMat
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil ValuativeRel
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib1

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem val_le_one_of_nabs_lt {t : kˣ} (ht : nabs k t < 1) : valuation k (t : k) ≤ 1 := by
  have h := (nabs_le_iff t 1).1 (by rw [nabs_one]; exact ht.le)
  simpa using h

theorem lat_le_inv {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {L : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) {t : kˣ} (ht : nabs k t < 1) : L ≤ ((t⁻¹ : kˣ) : k) • L := by
  intro x hx
  refine (AddSubgroup.mem_smul_pointwise_iff_exists x _ L).2 ⟨(t : k) • x, hL.int _ (val_le_one_of_nabs_lt ht) x hx, ?_⟩
  simp [smul_smul]

theorem lat_smul_le {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {L : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) {t : kˣ} (ht : nabs k t < 1) (j : ℕ) : ((t ^ j : kˣ) : k) • L ≤ L := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists x _ L).1 hx
  refine hL.int _ ?_ y hy
  rw [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_one' (val_le_one_of_nabs_lt ht) j

end PositivityTheory.RgUd.TP.Nil.Fib1
