import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleSqSubMulSq
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdele_sq_sub_mul_sq_eq_of_local : ∀ (K : Type) [Field K] [NumberField K] (δ a : K), δ ≠ 0 → a ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 K), ∃ x y : v.adicCompletion K, x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 = algebraMap K (v.adicCompletion K) a) → ∃ x y : FiniteAdeleRing (𝓞 K) K, x ^ 2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) δ * y ^ 2 = algebraMap K (FiniteAdeleRing (𝓞 K) K) a := by
  first | (exact @GlobalTheory.AdelicQuadSol.exists_finiteAdele_sq_sub_mul_sq) | (exact GlobalTheory.AdelicQuadSol.exists_finiteAdele_sq_sub_mul_sq) | (intros; apply GlobalTheory.AdelicQuadSol.exists_finiteAdele_sq_sub_mul_sq  <;> assumption)
