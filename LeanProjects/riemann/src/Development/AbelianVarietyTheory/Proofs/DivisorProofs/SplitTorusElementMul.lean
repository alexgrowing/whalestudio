import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.IdTorus
theorem isIdTorusElt_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} {l l' : Fin r → (AF F ⊗[F] E)ˣ} {a b : GAd σ J}
    (ha : IsIdTorusElt σ J X Y l a) (hb : IsIdTorusElt σ J X Y l' b) : IsIdTorusElt σ J X Y (l * l') (a * b) := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  refine ⟨?_, ?_, fun z hz => ?_⟩
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb1, ← Matrix.mul_assoc, ha1, Matrix.mul_assoc, diagonal_mul_diagonal]
    exact congrArg _ (congrArg _ (funext fun k => by simp))
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb2, ← Matrix.mul_assoc, ha2, Matrix.mul_assoc, diagonal_mul_diagonal]
    exact congrArg _ (congrArg _ (funext fun k => by simp [map_mul, mul_inv, Units.val_mul, mul_comm]))
  · rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hb3 z hz, ha3 z hz]
end GlobalTheory.IdTorus
