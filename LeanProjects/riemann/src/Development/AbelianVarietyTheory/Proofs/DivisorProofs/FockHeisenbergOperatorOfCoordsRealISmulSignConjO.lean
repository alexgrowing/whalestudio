import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.HeisRot

theorem jm_eq (p q : ℕ) : Jm p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  unfold Jm Formalism.UG.Jpq
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp

theorem jm_conj_apply {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (a : Ix P Q) (b : Ix R S) :
    (Jm P Q * c * Jm R S) a b = lineSign a b * c a b := by
  rw [jm_eq, jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem term_eq {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (t : ℝ) (l : Ln P Q R S) :
    ((((t : ℂ) * Complex.I) • (Jm P Q * c * Jm R S)) l.1 l.2 • raiB l
      - (lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 *
          star ((((t : ℂ) * Complex.I) • (Jm P Q * c * Jm R S)) l.1 l.2)) • lowB l)
        (1 : Formalism.BasicNotions.TH.Pol P Q R S)
      = ((t : ℂ) * Complex.I) • ((c l.1 l.2 • raiB l
          - (lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 * star (c l.1 l.2)) • lowB l)
        (1 : Formalism.BasicNotions.TH.Pol P Q R S)) := by
  obtain ⟨a, b⟩ := l
  rw [Matrix.smul_apply, jm_conj_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [raiB, lowB, linePos, lineSign, Complex.conj_ofReal, smul_smul] <;> ring_nf

theorem heisOp_rot_one (P Q R S : ℕ) (c : Matrix (Ix P Q) (Ix R S) ℂ) (t : ℝ) :
    heisOp (((t : ℂ) * Complex.I) • (Jm P Q * c * Jm R S)) 1 = ((t : ℂ) * Complex.I) • heisOp c 1 := by
  unfold heisOp
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sum_apply,
    Finset.sum_congr rfl (fun l _ => term_eq c t l), ← Finset.smul_sum, smul_comm]

end GlobalTheory.HeisRot
