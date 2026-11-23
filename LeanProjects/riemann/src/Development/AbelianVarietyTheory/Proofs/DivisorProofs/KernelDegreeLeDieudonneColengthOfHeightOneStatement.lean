import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColengthOfHeightOne
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelDegree_le_dieudonneColength_of_heightOne : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ), q ≫ q' = (p : ℤ_[p]) • 𝟙 G → q' ≫ q = (p : ℤ_[p]) • 𝟙 H → frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1) → HasLogDeg q e → (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧ (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M H.dual ⧸ LinearMap.range (T.map (dualHom G H q))) ∧ e ≤ Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) := by
  first | exact @GlobalTheory.Dieu.le_colength_of_htOne | exact GlobalTheory.Dieu.le_colength_of_htOne | (intros; apply GlobalTheory.Dieu.le_colength_of_htOne <;> assumption)
