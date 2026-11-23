import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free

def hypOne {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    Matrix (Fin (M + 2)) (Fin (M + 2)) K :=
  Matrix.of (Fin.cons (Fin.cons 0 (Fin.cons 1 fun _ => 0))
    (Fin.cons (Fin.cons 1 (Fin.cons 0 fun _ => 0)) fun i => Fin.cons 0 (Fin.cons 0 (A i))))

section Entries

variable {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)

theorem hypOne_zero_zero : hypOne A 0 0 = 0 := rfl
theorem hypOne_zero_one : hypOne A 0 1 = 1 := rfl
theorem hypOne_one_zero : hypOne A 1 0 = 1 := rfl
theorem hypOne_one_one : hypOne A 1 1 = 0 := rfl
theorem hypOne_zero_rest (j : Fin M) : hypOne A 0 j.succ.succ = 0 := rfl
theorem hypOne_one_rest (j : Fin M) : hypOne A 1 j.succ.succ = 0 := rfl
theorem hypOne_rest_zero (i : Fin M) : hypOne A i.succ.succ 0 = 0 := rfl
theorem hypOne_rest_one (i : Fin M) : hypOne A i.succ.succ 1 = 0 := rfl
theorem hypOne_rest_rest (i j : Fin M) : hypOne A i.succ.succ j.succ.succ = A i j := rfl

end Entries

end GlobalTheory.CompanionTheory.WeilSiegel.Free
