import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesPair

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)

theorem sum_pr_star {N : ℕ} (x y : Fin N → D.host.E) :
    ∑ r, p.pr (x r) * p.pr (star (y r)) = p.pr (star (star x ⬝ᵥ y)) := by
  change ∑ r, Witness.prH p (x r) * Witness.prH p (star (y r)) = Witness.prH p (star (star x ⬝ᵥ y))
  rw [dotProduct, star_sum, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Pi.star_apply, star_mul, star_star, map_mul]
  ring

theorem col_pair {N : ℕ} {ι τ : Type} [Fintype ι] (X : Matrix (Fin N) ι D.host.E)
    (G : Matrix (Fin N) (Fin N) D.host.E) (e : Matrix (Fin N) τ D.host.E) (j : ι) (i : τ) :
    star (fun r => X r j) ⬝ᵥ (G *ᵥ fun r => e r i) = (Xᴴ * G * e) j i := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  rfl

theorem mulVec_col {N M : ℕ} {τ : Type} (A : Matrix (Fin M) (Fin N) D.host.E) (e : Matrix (Fin N) τ D.host.E) (i : τ) :
    (A *ᵥ fun r => e r i) = fun u => (A * e) u i := by
  funext u
  rfl

theorem pr_zero : p.pr (0 : D.host.E) = 0 := (Witness.prH p).map_zero

theorem pr_one : p.pr (1 : D.host.E) = 1 := (Witness.prH p).map_one

theorem bes_cols : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (ρ : ℕ) (B : BesLev D ρ) (s : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)),
    p.IsBesFrame B s FA F → valuation k s = 1 → valuation k (p.hz B) = 1 → valuation k p.xi = 1 → ∀ i : Fin ρ,
    ∃ (b : k) (m₀ : n ⊕ Fin c), valuation k b = 1 ∧ (∀ r, b * p.pr (B.d.e r i) = F.β r m₀) ∧
      (∀ m, ∑ r, F.β r m * p.pr (star ((B.V.gram *ᵥ fun r => B.d.e r i) r)) ∈ 𝒪[k]) ∧
      ∃ m, valuation k (∑ r, F.β r m * p.pr (star ((B.V.gram *ᵥ fun r => B.d.e r i) r))) = 1 := by
  intro D k _ _ _ _ p ρ B s n _ _ c FA F h hs hz hx i
  obtain ⟨rfl, h1, h2, h3, h4⟩ := h
  have hC : ∀ t : ℕ, valuation k (s * (-p.hz B / p.xi) * (-1 / p.xi) ^ t) = 1 := by
    intro t
    simp [map_mul, map_div₀, Valuation.map_neg, map_pow, hs, hz, hx]

  have hval : ∀ (i' : Fin ρ) (j : Fin (2 * ρ + 1)), j.val + i'.val = 2 * ρ →
      ∑ r, F.β r (Sum.inr j) * p.pr (star ((B.V.gram *ᵥ fun r => B.d.e r i) r)) =
        s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i'.val) * p.pr (star ((1 : Matrix (Fin ρ) (Fin ρ) D.host.E) i' i)) := by
    intro i' j hj
    simp_rw [h4 i' j hj, mul_assoc, ← Finset.mul_sum]
    rw [sum_pr_star, col_pair, B.d.e'e]
  have hq : ∀ m, (∑ r, F.β r m * p.pr (star ((B.V.gram *ᵥ fun r => B.d.e r i) r))) = 0 ∨
      valuation k (∑ r, F.β r m * p.pr (star ((B.V.gram *ᵥ fun r => B.d.e r i) r))) = 1 := by
    rintro (a | ⟨j, hj⟩)
    · left
      have hM : (B.d.i₀ * B.o.iA)ᴴ * B.V.gram * B.d.e = 0 := by
        rw [Matrix.conjTranspose_mul,
          show B.o.iAᴴ * B.d.i₀ᴴ * B.V.gram * B.d.e = B.o.iAᴴ * (B.d.i₀ᴴ * B.V.gram * B.d.e) by
            simp only [Matrix.mul_assoc],
          B.d.i₀e, Matrix.mul_zero]
      simp_rw [h1, Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun u _ => ?_
      calc ∑ r, p.pr ((B.d.i₀ * B.o.iA) r u) * FA.β u a * p.pr (star ((B.V.gram *ᵥ fun r => B.d.e r i) r))
          = (∑ r, p.pr ((B.d.i₀ * B.o.iA) r u) * p.pr (star ((B.V.gram *ᵥ fun r => B.d.e r i) r))) * FA.β u a := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
        _ = 0 := by
            rw [sum_pr_star p (fun r => (B.d.i₀ * B.o.iA) r u), col_pair, hM, Matrix.zero_apply, star_zero, pr_zero,
              zero_mul]
    · rcases lt_trichotomy j ρ with hlt | heq | hgt
      · left
        simp_rw [h2 ⟨j, hlt⟩ ⟨j, hj⟩ rfl, mul_assoc, ← Finset.mul_sum]
        rw [sum_pr_star, col_pair, B.d.ee, Matrix.zero_apply, star_zero, pr_zero, mul_zero, mul_zero]
      · left
        simp_rw [h3 ⟨j, hj⟩ heq, mul_assoc, ← Finset.mul_sum]
        rw [sum_pr_star, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, mulVec_col, B.d.i₀e]
        simp only [Matrix.zero_apply]
        rw [dotProduct_zero', star_zero, pr_zero, mul_zero]
      · have hi' : 2 * ρ - j < ρ := by omega
        rw [hval ⟨2 * ρ - j, hi'⟩ ⟨j, hj⟩ (by simp only; omega)]
        by_cases he : (⟨2 * ρ - j, hi'⟩ : Fin ρ) = i
        · right
          rw [he, Matrix.one_apply_eq, star_one, pr_one, mul_one]
          exact hC _
        · left
          rw [Matrix.one_apply_ne he, star_zero, pr_zero, mul_zero]
  refine ⟨s * p.xi ^ (ρ - i.val), Sum.inr ⟨i.val, by omega⟩, ?_, fun r => (h2 i _ rfl r).symm, fun m => ?_, ?_⟩
  · simp [map_mul, map_pow, hs, hx]
  · rw [Valuation.mem_integer_iff]
    rcases hq m with h0 | h0
    · rw [h0, map_zero]; exact zero_le'
    · exact h0.le
  · refine ⟨Sum.inr ⟨2 * ρ - i.val, by omega⟩, ?_⟩
    rw [hval i _ (by simp only; omega), Matrix.one_apply_eq, star_one, pr_one, mul_one]
    exact hC _

end GlobalTheory.BesPair
end
