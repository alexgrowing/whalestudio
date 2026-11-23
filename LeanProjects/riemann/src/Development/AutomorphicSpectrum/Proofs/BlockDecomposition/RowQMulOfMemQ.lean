import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMatMir

noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun Matrix

namespace GlobalTheory.CompanionTheory.BZPhiPhi

theorem rowQ_mul_of_mem_Q (k : Type) [Field k] (n : ℕ) (q g : Mir k (n + 1)) (hq : q ∈ Q k n) :
    rowQ k n (q * g) = rowQ k n g := by
  have hb : (blockMat k (n + 1) ((q : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k)) (Fin.last n) =
      eLast k n := by
    have h := (mem_Mir_iff k (mirabolicProjection k (n + 1) q)).1 hq
    exact h
  have hg : ∀ j : Fin (n + 1), ((g : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k)
      (Fin.last (n + 1)) (Fin.castSucc j) = 0 := by
    intro j
    have := congrFun ((mem_Mir_iff k (g : GL (Fin (n + 2)) k)).1 g.2) (Fin.castSucc j)
    simpa [eLast, Fin.castSucc_ne_last] using this
  funext j
  have hb' : ∀ l : Fin (n + 1), ((q : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k)
      (Fin.castSucc (Fin.last n)) (Fin.castSucc l) = eLast k n l := fun l => congrFun hb l
  simp only [rowQ, Subgroup.coe_mul, Units.val_mul, mul_apply, Fin.sum_univ_castSucc (n := n + 1), hg, hb', mul_zero, add_zero]
  simp [eLast, Pi.single_apply]

end GlobalTheory.CompanionTheory.BZPhiPhi

end
