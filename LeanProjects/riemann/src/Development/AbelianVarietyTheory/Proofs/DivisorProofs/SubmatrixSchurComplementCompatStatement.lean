import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmatrixSchurComplementCompat
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.submatrix_schur_complement_compat : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] (m m' t l : Type) [Fintype m] [Fintype m'] [Fintype t] [Fintype l] [DecidableEq m] [DecidableEq m'] [DecidableEq t] [DecidableEq l] (e : m' ⊕ t ≃ m), (∀ (K : Matrix (m ⊕ l) (m ⊕ l) ℂ) (K' : Matrix (m' ⊕ l) (m' ⊕ l) ℂ), K.submatrix (Sum.map (fun a => e (Sum.inl a)) id) (Sum.map (fun a => e (Sum.inl a)) id) = K' → (∀ (a : m' ⊕ l) (b : t), K (Sum.map (fun a => e (Sum.inl a)) id a) (Sum.inl (e (Sum.inr b))) = 0 ∧ K (Sum.inl (e (Sum.inr b))) (Sum.map (fun a => e (Sum.inl a)) id a) = 0) → IsUnit (GlobalTheory.HermFrame.subGram K).det → GlobalTheory.HermFrame.quotGram K = GlobalTheory.HermFrame.quotGram K') ∧ ∀ (K : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (K' : V → Matrix (m' ⊕ l) (m' ⊕ l) ℂ) (z : V), (∀ᶠ x in nhds z, (K x).submatrix (Sum.map (fun a => e (Sum.inl a)) id) (Sum.map (fun a => e (Sum.inl a)) id) = K' x ∧ (∀ (a : m' ⊕ l) (b : t), K x (Sum.map (fun a => e (Sum.inl a)) id a) (Sum.inl (e (Sum.inr b))) = 0 ∧ K x (Sum.inl (e (Sum.inr b))) (Sum.map (fun a => e (Sum.inl a)) id a) = 0) ∧ IsUnit (GlobalTheory.HermFrame.subGram (K x)).det) → GlobalTheory.HermFrame.extTrace K z = GlobalTheory.HermFrame.extTrace K' z := by
  first | exact @GlobalTheory.HermFrame.quotGram_extTrace_of_orthogonal_summand | exact GlobalTheory.HermFrame.quotGram_extTrace_of_orthogonal_summand | (intros; apply GlobalTheory.HermFrame.quotGram_extTrace_of_orthogonal_summand <;> assumption)
