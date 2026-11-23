import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactFundamentalSet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_witt_basis_compact_stabiliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (l : E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E), l ≠ 0 → J.det ≠ 0 → J₂ = dblGram finSumFinEquiv J → ∃ (T : GL (Fin (n + n)) E) (K : Subgroup (UA σ J₂)), IsWittBasis σ J l T ∧ IsStdK σ T K ∧ IsCompact (K : Set (UA σ J₂)) := by
  first | exact @GlobalTheory.SWLit.WittStd.exists_wittBasis_stdK | exact GlobalTheory.SWLit.WittStd.exists_wittBasis_stdK | (intros; apply GlobalTheory.SWLit.WittStd.exists_wittBasis_stdK <;> assumption)
