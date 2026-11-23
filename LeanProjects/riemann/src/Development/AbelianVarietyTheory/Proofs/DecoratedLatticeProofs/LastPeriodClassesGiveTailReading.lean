import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem tailRd_of_clsT : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsT ρ t), A.Is → t.cP ≠ 0 → t.TailRd := by
  intro D c t ρ A hA hcP n h ψ hψ ψ' hψ' a H F
  have e1 := hA.tail n h ψ hψ F
  have e2 := hA.tail n h ψ' hψ' F
  have key : ∀ β (x : A.cl), A.ell n h β x F (ρ.low n h fun z => t.rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) =
      a * A.ell n h β x F (ρ.low n h fun z => t.rd n β ψ' ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) := by
    intro β x
    have : (fun z => t.rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) =
        a • (fun z => t.rd n β ψ' ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) := by
      funext z
      rw [H β ((ρ.fr n).symm z)]
      rfl
    rw [this, map_smul, map_smul, smul_eq_mul]
  simp_rw [key] at e1
  have e3 : t.cP * t.tail n h ψ F = t.cP * (a * t.tail n h ψ' F) := by
    rw [← e1, mul_left_comm t.cP a, ← e2]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  exact mul_left_cancel₀ hcP e3

end GlobalTheory.SeeSaw

end
