import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeierstrassPFamilySeparatingGl2ZMod
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weierstrassP_family_separating_gl2ZMod : ∀ (N : ℕ) [NeZero N], ∃ c₁ c₂ : ℕ, ∀ α β : GL (Fin 2) (ZMod N), (fun τ => wp N (vmul ![1, 0] α) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] α) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] α) τ) = (fun τ => wp N (vmul ![1, 0] β) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] β) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] β) τ) → α = β ∨ α = -β := by
  first | exact @GlobalTheory.FNSep.sep_family | exact GlobalTheory.FNSep.sep_family | (intros; apply GlobalTheory.FNSep.sep_family <;> assumption)
