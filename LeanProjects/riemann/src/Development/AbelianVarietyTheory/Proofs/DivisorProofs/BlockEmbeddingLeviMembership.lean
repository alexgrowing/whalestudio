import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Gl2LocalToAdelicEmbedding
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MemSpanCentreTranslates
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.IdTorus GlobalTheory.GLTwoHecke
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut (IsMaxCpt)
open GlobalTheory.StdPar

noncomputable section

namespace GlobalTheory.GLTwoHecke.BlockLevi

section Mat

variable {A : Type} [CommRing A]

variable (A) in

def incl (m : ℕ) : Matrix (Fin m) (Fin 2) A := fun a b => if a.val = b.val then 1 else 0

theorem inclT_incl {m : ℕ} (hm : 2 ≤ m) : (incl A m)ᵀ * incl A m = 1 := by
  ext c d
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨c.val, by omega⟩]
  · by_cases h : c = d
    · subst h; simp [incl]
    · have : c.val ≠ d.val := fun e => h (Fin.ext e)
      simp [incl, this, Matrix.one_apply_ne h]
  · intro a _ ha
    have : a.val ≠ c.val := fun e => ha (Fin.ext e)
    simp [incl, this]
  · simp

def blk (m : ℕ) (H : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin m) (Fin m) A :=
  1 + incl A m * (H - 1) * (incl A m)ᵀ

theorem blk_mul {m : ℕ} (hm : 2 ≤ m) (H H' : Matrix (Fin 2) (Fin 2) A) : blk m H * blk m H' = blk m (H * H') := by
  have hi := inclT_incl (A := A) hm
  have e : H * H' - 1 = (H - 1) + (H' - 1) + (H - 1) * (H' - 1) := by noncomm_ring
  have p : incl A m * (H - 1) * (incl A m)ᵀ * (incl A m * (H' - 1) * (incl A m)ᵀ) =
      incl A m * ((H - 1) * (H' - 1)) * (incl A m)ᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl A m)ᵀ (incl A m), hi, Matrix.one_mul]
  simp only [blk]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, p, e,
    Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  abel

def blkHom {m : ℕ} (hm : 2 ≤ m) : Matrix (Fin 2) (Fin 2) A →* Matrix (Fin m) (Fin m) A where
  toFun := blk m
  map_one' := by simp [blk]
  map_mul' := fun a b => (blk_mul hm a b).symm

def blkGL {m : ℕ} (hm : 2 ≤ m) : GL (Fin 2) A →* GL (Fin m) A := Units.map (blkHom hm)

@[simp] theorem blkGL_val {m : ℕ} (hm : 2 ≤ m) (h : GL (Fin 2) A) : (blkGL hm h).1 = blk m h.1 := rfl

end Mat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.GLTwoHecke.BlockLevi

end
