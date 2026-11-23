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

namespace GlobalTheory.BesPair

theorem besz_pairings : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (ρ : ℕ) (B : BesLev D ρ) (s : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)),
    p.IsBesFrame B s FA F → valuation k s = 1 → valuation k (p.hz B) = 1 →
    ∃ m₀ : n ⊕ Fin c, (∀ r, s * p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r) = F.β r m₀) ∧
      (∀ m, ∑ r, F.β r m * p.pr (star ((B.V.gram *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ)) r)) ∈ 𝒪[k]) ∧
      ∃ m, valuation k (∑ r, F.β r m * p.pr (star ((B.V.gram *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ)) r))) = 1 := by
  intro D k _ _ _ _ p ρ B s n _ _ c FA F hF hs hz
  obtain ⟨rfl, h1, h2, h3, h4⟩ := hF
  have hG := GlobalTheory.MixModel.gram_conjTranspose (S := B.V)
  have hp0 : p.pr 0 = 0 := map_zero (GlobalTheory.LocMod.Witness.prH p)
  have hl : ∀ r, p.pr (star ((B.V.gram *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ)) r)) =
      p.pr ((star (B.d.i₀ *ᵥ vecB B.o B.ζ) ᵥ* B.V.gram) r) := fun r => by
    conv_rhs => rw [← hG, ← Matrix.star_mulVec]
    rfl
  have hM : ∀ {ι : Type} [Fintype ι] (M : Matrix (Fin B.V.rank) ι D.host.E),
      star (B.d.i₀ *ᵥ vecB B.o B.ζ) ᵥ* B.V.gram ᵥ* M = star (vecB B.o B.ζ) ᵥ* (B.d.i₀ᴴ * B.V.gram * M) := fun M => by
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  have hsum : ∀ (t : k) {ι : Type} [Fintype ι] (M : Matrix (Fin B.V.rank) ι D.host.E) (i : ι),
      ∑ r, t * p.pr (M r i) * p.pr ((star (B.d.i₀ *ᵥ vecB B.o B.ζ) ᵥ* B.V.gram) r) =
        t * p.pr ((star (B.d.i₀ *ᵥ vecB B.o B.ζ) ᵥ* B.V.gram ᵥ* M) i) := by
    intro t ι _ M i
    change _ = t * GlobalTheory.LocMod.Witness.prH p _
    rw [Matrix.vecMul, dotProduct, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul]
    change t * GlobalTheory.LocMod.Witness.prH p (M r i) * GlobalTheory.LocMod.Witness.prH p _ =
      t * (GlobalTheory.LocMod.Witness.prH p _ * GlobalTheory.LocMod.Witness.prH p (M r i))
    ring
  have hE : star (B.d.i₀ *ᵥ vecB B.o B.ζ) ᵥ* B.V.gram ᵥ* B.d.e = 0 := by
    rw [hM, B.d.i₀e, Matrix.vecMul_zero]
  have hE' : star (B.d.i₀ *ᵥ vecB B.o B.ζ) ᵥ* B.V.gram ᵥ* B.d.e' = 0 := by
    rw [hM, B.d.i₀e', Matrix.vecMul_zero]
  have hA : star (B.d.i₀ *ᵥ vecB B.o B.ζ) ᵥ* B.V.gram ᵥ* (B.d.i₀ * B.o.iA) = 0 := by
    rw [hM, ← Matrix.mul_assoc, B.d.iso, vecB, Matrix.star_mulVec, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, B.o.orth,
      Matrix.vecMul_zero]
  have hdot : (star (B.d.i₀ *ᵥ vecB B.o B.ζ) ᵥ* B.V.gram) ⬝ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ := by
    rw [Matrix.dotProduct_mulVec, hM, B.d.iso, vecB, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
    simp only [Matrix.vecMul_vecMul]
    rw [B.o.isoB, ← Matrix.dotProduct_mulVec]
  have hcore : ∀ a, ∑ r, F.β r (Sum.inl a) * p.pr (star ((B.V.gram *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ)) r)) = 0 := by
    intro a
    simp_rw [h1, hl, Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    have := hsum (FA.β b a) (B.d.i₀ * B.o.iA) b
    rw [hA, Pi.zero_apply, hp0, mul_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hval : ∀ j : Fin (2 * ρ + 1), j.val = ρ →
      ∑ r, F.β r (Sum.inr j) * p.pr (star ((B.V.gram *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ)) r)) = s * p.hz B := by
    intro j hj
    simp_rw [h3 j hj, hl]
    change _ = s * GlobalTheory.LocMod.Witness.prH p _
    rw [← hdot, dotProduct, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul]
    change s * GlobalTheory.LocMod.Witness.prH p _ * GlobalTheory.LocMod.Witness.prH p _ =
      s * (GlobalTheory.LocMod.Witness.prH p _ * GlobalTheory.LocMod.Witness.prH p _)
    ring
  have hunit : valuation k (s * p.hz B) = 1 := by rw [map_mul, hs, hz, one_mul]
  refine ⟨Sum.inr ⟨ρ, by omega⟩, fun r => (h3 _ rfl r).symm, fun m => ?_, Sum.inr ⟨ρ, by omega⟩, by rw [hval _ rfl, hunit]⟩
  rcases m with a | j
  · rw [hcore a]; exact zero_mem _
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · simp_rw [h2 ⟨j.val, hj⟩ j rfl, hl]
    rw [hsum, hE, Pi.zero_apply, hp0, mul_zero]; exact zero_mem _
  · rw [hval j hj]
    exact (Valuation.mem_integer_iff _ _).2 (le_of_eq hunit)
  · have hj2 := j.isLt
    simp_rw [h4 ⟨2 * ρ - j.val, by omega⟩ j (by simp only; omega), hl]
    rw [hsum, hE', Pi.zero_apply, hp0, mul_zero]; exact zero_mem _
end GlobalTheory.BesPair
