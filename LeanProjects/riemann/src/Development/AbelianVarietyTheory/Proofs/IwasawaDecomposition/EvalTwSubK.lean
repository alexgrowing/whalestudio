import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply

noncomputable section

namespace GlobalTheory.IntegralityCompare

open MvPolynomial

def twSubK {E K ι : Type} [Field E] [Field K] [Fintype ι] {n : ℕ} (t : ι → E →+* K) (M : GL (Fin n) E) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) K) : MvPolynomial (ι × Fin n × Fin n) K :=
  C (∏ τ, (t τ (M : Matrix (Fin n) (Fin n) E).det) ^ (s τ)) *
    bind₁ (fun k : ι × Fin n × Fin n => ∑ j : Fin n,
      C (t k.1 ((M : Matrix (Fin n) (Fin n) E) k.2.1 j)) * X (k.1, j, k.2.2)) P

open MvPolynomial in
theorem _root_.GlobalTheory.IntegralityCompare.map_twSubK {E K ι : Type} [Field E] [Field K] [Fintype ι] {n : ℕ}
    (t : ι → E →+* K) (M : GL (Fin n) E) (s : ι → ℤ) (P : MvPolynomial (ι × Fin n × Fin n) K)
    (φ : K →+* ℂ) :
    map φ (_root_.GlobalTheory.IntegralityCompare.twSubK t M s P) =
      _root_.GlobalTheory.IntegralityCompare.twSub (fun τ => φ.comp (t τ)) M s (map φ P) := by
  rw [_root_.GlobalTheory.IntegralityCompare.twSubK, _root_.GlobalTheory.IntegralityCompare.twSub, map_mul, map_C, map_bind₁]
  simp [map_prod, map_zpow₀]

open MvPolynomial in
private lemma eval_bind_eq_eval_comp {K σ τ : Type} [CommRing K] (f : σ → MvPolynomial τ K)
    (x : τ → K) (P : MvPolynomial σ K) :
    eval x (bind₁ f P) = eval (fun i => eval x (f i)) P := by
  rw [← aeval_eq_eval, ← aeval_eq_eval, aeval_bind₁]

open MvPolynomial in
theorem _root_.GlobalTheory.IntegralityCompare.eval_twSubK {E K ι : Type} [Field E] [Field K] [Fintype ι] {n : ℕ}
    (t : ι → E →+* K) (M : GL (Fin n) E) (s : ι → ℤ) (P : MvPolynomial (ι × Fin n × Fin n) K)
    (x : ι → Matrix (Fin n) (Fin n) K) :
    eval (fun k : ι × Fin n × Fin n => x k.1 k.2.1 k.2.2) (_root_.GlobalTheory.IntegralityCompare.twSubK t M s P) =
      (∏ τ, (t τ (M : Matrix (Fin n) (Fin n) E).det) ^ (s τ)) *
        eval (fun k : ι × Fin n × Fin n =>
          (((M : Matrix (Fin n) (Fin n) E).map (t k.1)) * x k.1) k.2.1 k.2.2) P := by
  rw [_root_.GlobalTheory.IntegralityCompare.twSubK, map_mul, eval_C, eval_bind_eq_eval_comp]
  congr 3
  funext k
  simp [Matrix.mul_apply, eval_sum]

end GlobalTheory.IntegralityCompare

end
