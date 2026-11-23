import Formalism.LocalToGlobal.GlobalTheory.BlockActions.BlkFockLe
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NfAllSmulReB

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms

section Gen

variable {ι : Type} [Fintype ι] {n : ℕ}

def rowSubK {R : Type} [CommRing R] (o : ι → Matrix (Fin n) (Fin n) R) :
    MvPolynomial (ι × Fin n × Fin n) R →ₐ[R] MvPolynomial (ι × Fin n × Fin n) R :=
  aeval fun x => ∑ a', C (o x.1 x.2.1 a') * X (x.1, a', x.2.2)

theorem rowSubK_eq_subP (o : ι → Matrix (Fin n) (Fin n) ℂ) : rowSubK o = subP o := rfl

theorem subP_eq_blkRow (o : ι → Matrix (Fin n) (Fin n) ℂ) : subP o = blkRow o := rfl

theorem map_rowSubK {R S : Type} [CommRing R] [CommRing S] (j : R →+* S) (o : ι → Matrix (Fin n) (Fin n) R)
    (P : MvPolynomial (ι × Fin n × Fin n) R) :
    map j (rowSubK o P) = rowSubK (fun τ => (o τ).map j) (map j P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowSubK, MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    simp [rowSubK, map_sum, Matrix.map_apply]

theorem blkRow_comp (K L : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    blkRow K (blkRow L P) = blkRow (fun τ => L τ * K τ) P := by
  have e : (blkRow K).comp (blkRow L) = blkRow (fun τ => L τ * K τ) := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply]
    simp only [blkRow, aeval_X, map_sum, map_mul, aeval_C, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← mul_assoc,
      MvPolynomial.algebraMap_eq]
    rw [Finset.sum_comm]
  rw [← e, AlgHom.comp_apply]

theorem norm_one_of_pow {K : Type} [Field K] (j s : K →+* ℂ) (a : K) (k : ℕ) (hk : 0 < k) (h : (j a) ^ k = 1) :
    ‖s a‖ = 1 := by
  have h1 : a ^ k = 1 := j.injective (by rw [map_pow, h, map_one])
  have h2 : (s a) ^ k = 1 := by rw [← map_pow, h1, map_one]
  have h3 := congrArg norm h2
  rw [norm_pow, norm_one] at h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h3

end Gen

end Formalism.L2.GlobalTheoryTheory.Br
