import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSplitRankOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_split_rank_one : ∀ {k R V : Type} [Field k] [CommRing R] [AddCommGroup V] [Module R V] (φ : R ≃+* k × k) (c : R →+* R), (∀ r, φ (c r) = (φ r).swap) → ∀ h : V → V → R, IsHerm c h → IsPerfect h → (∀ x y, h x x = 0 → h x y ≠ 1) → Subsingleton V ∨ ∃ w₀ : V, (∀ x, ∃ r : R, x = r • w₀) ∧ IsUnit (h w₀ w₀) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.hermSwap_struct | exact GlobalTheory.CompanionTheory.KFin.hermSwap_struct | (intros; apply GlobalTheory.CompanionTheory.KFin.hermSwap_struct <;> assumption)
