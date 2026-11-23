import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCharacterSumEqLocallyConstantOnCompaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactCharAnnihilatorOfMemNhdsZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenRowVectorOrbitCompactOpenGLStatement

open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin

theorem eqv_cor_mul_col {F : Type} [NormedField F] {ψ : AddChar F ℂ} {m : ℕ} {W : GL (Fin (m + 2)) F → ℂ}
    (hW : Eqv ψ W) (h : GL (Fin (m + 1)) F) (x : Fin (m + 1) → F) :
    W (cor h * mir 1 x) = ψ (lr h ⬝ᵥ x) * W (cor h) := by
  change W (mir h 0 * mir 1 x) = _
  rw [mir_mul, hW.apply_mir, mul_one, add_zero]
  rfl

theorem eqv_act {F : Type} [NormedField F] {ψ : AddChar F ℂ} {n : ℕ} {W : GL (Fin n) F → ℂ}
    (hW : Eqv ψ W) (T : GL (Fin n) F →₀ ℂ) : Eqv ψ (act T W) := fun u hu g => by
  unfold act
  rw [Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only
  rw [mul_assoc u, hW u hu]
  ring

theorem lr_ne_zero {F : Type} [NormedField F] {m : ℕ} (h : GL (Fin (m + 1)) F) : lr h ≠ 0 := fun h0 => by
  have h1 : lr (h * h⁻¹) = 0 := by rw [lr_mul, h0, zero_vecMul]
  rw [mul_inv_cancel] at h1
  have := congrFun h1 (Fin.last m)
  simp [lr] at this

end GlobalTheory.JSW.Cut
