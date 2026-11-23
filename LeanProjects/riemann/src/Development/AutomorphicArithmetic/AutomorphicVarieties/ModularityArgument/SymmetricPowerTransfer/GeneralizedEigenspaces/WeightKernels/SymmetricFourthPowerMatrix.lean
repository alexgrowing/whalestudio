import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.SlopeTestRemainingChoices

noncomputable section

open UpperTheory.V.Af

namespace UpperTheory.V.Z.Sym.Ga

set_option maxHeartbeats 4000000 in

def symmetricFourthPowerMatrix (R : Type) [CommRing R] : Matrix (Fin 2) (Fin 2) R →* Matrix (Fin 5) (Fin 5) R where
  toFun g := !![g 0 0 ^ 4, g 0 0 ^ 3 * g 0 1, g 0 0 ^ 2 * g 0 1 ^ 2, g 0 0 * g 0 1 ^ 3, g 0 1 ^ 4;
    4 * g 0 0 ^ 3 * g 1 0, g 0 0 ^ 3 * g 1 1 + 3 * g 0 0 ^ 2 * g 1 0 * g 0 1, 2 * g 0 0 ^ 2 * g 0 1 * g 1 1 + 2 * g 0 0 * g 1 0 * g 0 1 ^ 2, 3 * g 0 0 * g 0 1 ^ 2 * g 1 1 + g 1 0 * g 0 1 ^ 3, 4 * g 0 1 ^ 3 * g 1 1;
    6 * g 0 0 ^ 2 * g 1 0 ^ 2, 3 * g 0 0 ^ 2 * g 1 0 * g 1 1 + 3 * g 0 0 * g 1 0 ^ 2 * g 0 1, g 0 0 ^ 2 * g 1 1 ^ 2 + 4 * g 0 0 * g 1 0 * g 0 1 * g 1 1 + g 1 0 ^ 2 * g 0 1 ^ 2, 3 * g 0 0 * g 0 1 * g 1 1 ^ 2 + 3 * g 1 0 * g 0 1 ^ 2 * g 1 1, 6 * g 0 1 ^ 2 * g 1 1 ^ 2;
    4 * g 0 0 * g 1 0 ^ 3, 3 * g 0 0 * g 1 0 ^ 2 * g 1 1 + g 1 0 ^ 3 * g 0 1, 2 * g 0 0 * g 1 0 * g 1 1 ^ 2 + 2 * g 1 0 ^ 2 * g 0 1 * g 1 1, g 0 0 * g 1 1 ^ 3 + 3 * g 1 0 * g 0 1 * g 1 1 ^ 2, 4 * g 0 1 * g 1 1 ^ 3;
    g 1 0 ^ 4, g 1 0 ^ 3 * g 1 1, g 1 0 ^ 2 * g 1 1 ^ 2, g 1 0 * g 1 1 ^ 3, g 1 1 ^ 4]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

variable {Γ k : Type} [Group Γ] [Field k]

def sym4 (ρ : Γ →* GL (Fin 2) k) : Γ →* GL (Fin 5) k :=
  tw ((Units.map (symmetricFourthPowerMatrix k)).comp ρ) ((Matrix.GeneralLinearGroup.det.comp ρ)⁻¹ ^ 2)

end UpperTheory.V.Z.Sym.Ga

end
