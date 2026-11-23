import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.DecaysZero

open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

private theorem herm_eq_zero_iff {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) :
    Formalism.QuantumDeterminants.herm (Jm ε) x y = 0 ↔ star x ⬝ᵥ (Jm ε *ᵥ y) = 0 := by
  have e : Formalism.QuantumDeterminants.herm (Jm ε) x y = star (star x ⬝ᵥ (Jm ε *ᵥ y)) := by
    simp only [Formalism.QuantumDeterminants.herm, Jm, dotProduct, Matrix.mulVec_diagonal, star_sum, Pi.star_apply, star_mul', star_star]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases ε i <;> simp <;> ring
  rw [e, star_eq_zero]

private theorem herm_keep {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * H * g = H) (x y : Fin n → ℂ) :
    Formalism.QuantumDeterminants.herm H (g *ᵥ x) (g *ᵥ y) = Formalism.QuantumDeterminants.herm H x y := by
  simp only [Formalism.QuantumDeterminants.herm]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem UpperTheory.Lit.Cusp.flagN_eq_NW :
    ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)), IsIsoC ε W →
      IsIsoFlag ε ![Module.finrank ℂ W] ![⊥, W] ∧ 1 ≤ Module.finrank ℂ W ∧ flagN ε ![⊥, W] = NW ε W ∧
        ∃ S : Subgroup (UJ ε), (S : Set (UJ ε)) = NW ε W := by
  intro n ε W hW
  have hl : (![⊥, W] : Fin (1 + 1) → Submodule ℂ (Fin n → ℂ)) (Fin.last 1) = W := rfl
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_, ?_, GlobalTheory.Dec.nwSub ε W, rfl⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    show Module.finrank ℂ W = Module.finrank ℂ (⊥ : Submodule ℂ (Fin n → ℂ)) + Module.finrank ℂ W
    rw [finrank_bot, zero_add]
  · rw [hl]
    intro x hx y hy
    exact (herm_eq_zero_iff ε x y).1 (hW.2 x hx y hy)
  · exact Submodule.one_le_finrank_iff.2 hW.1
  · ext g
    have e : ∀ y, (umat g - 1) *ᵥ y = uMat g *ᵥ y - y := fun y => by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [flagN, NW, Set.mem_setOf_eq, hl, e]
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : ∀ x ∈ W, uMat g *ᵥ x - x = 0 := fun x hx => (Submodule.mem_bot ℂ).1 (h1 0 x hx)
      refine ⟨h1', fun y hy => h2 y fun x hx => (herm_eq_zero_iff ε x y).1 (hy x hx), fun y x hx => ?_⟩
      have hg : (uMat g)ᴴ * Jm ε * uMat g = Jm ε := g.2
      have k := herm_keep hg x y
      rw [sub_eq_zero.1 (h1' x hx)] at k
      simp only [Formalism.QuantumDeterminants.herm, star_sub, sub_dotProduct] at k ⊢
      rw [k, sub_self]
    · rintro ⟨h1, h2, -⟩
      refine ⟨fun i y hy => ?_, fun y hy => h2 y fun x hx => (herm_eq_zero_iff ε x y).2 (hy x hx)⟩
      fin_cases i
      exact (Submodule.mem_bot ℂ).2 (h1 y hy)
