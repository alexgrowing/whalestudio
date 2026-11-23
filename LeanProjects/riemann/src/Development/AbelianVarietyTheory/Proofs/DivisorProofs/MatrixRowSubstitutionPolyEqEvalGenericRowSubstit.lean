import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenCoef.RowSubstSum

def evY (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) :
    MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) →+* MvPolynomial (Fin N × Fin N) R :=
  eval₂Hom (MvPolynomial.map (algebraMap O R)) (fun v => C (Y v.1 v.2))

theorem evY_genSub (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R)
    (f : MvPolynomial (Fin N × Fin N) O) : evY O N R Y (GlobalTheory.HighWt.genSub O N f) = rowSubst O N R Y f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp [evY, GlobalTheory.HighWt.genSub, rowSubst, MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    simp only [GlobalTheory.HighWt.genSub, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p v hp =>
    simp only [GlobalTheory.HighWt.genSub, map_mul] at hp ⊢
    rw [hp]
    congr 1
    simp [evY, rowSubst, map_sum]

theorem evY_eq_sum (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R)
    (P : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O)) :
    evY O N R Y P = ∑ m ∈ P.support, (m.prod fun v k => Y v.1 v.2 ^ k) • MvPolynomial.map (algebraMap O R) (P.coeff m) := by
  simp only [evY, coe_eval₂Hom, MvPolynomial.eval₂, Finsupp.sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h : (m.prod fun v k => (C (Y v.1 v.2) : MvPolynomial (Fin N × Fin N) R) ^ k) = C (m.prod fun v k => Y v.1 v.2 ^ k) := by
    simp [Finsupp.prod, map_prod, map_pow]
  rw [h, mul_comm, C_mul']
  rfl

theorem main : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) (f : MvPolynomial (Fin N × Fin N) O), rowSubst O N R Y f = ∑ m ∈ (GlobalTheory.HighWt.genSub O N f).support, (m.prod fun v k => Y v.1 v.2 ^ k) • MvPolynomial.map (algebraMap O R) ((GlobalTheory.HighWt.genSub O N f).coeff m) := by
  intro O _ N R _ _ Y f
  rw [← evY_genSub, evY_eq_sum]

end GlobalTheory.GenCoef.RowSubstSum

end
