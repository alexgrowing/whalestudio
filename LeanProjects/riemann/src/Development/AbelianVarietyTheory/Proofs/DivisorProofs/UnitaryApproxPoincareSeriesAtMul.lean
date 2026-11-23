import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
import Development.AbelianVarietyTheory.Definitions.Divisors.UApproxAtZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem uApproxAt_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (φ : InvFun (𝓞 E)) (d m : ℕ), 1 ≤ m → UApproxAt X₁ φ d → UApproxAt X₁ φ (d * m) := by
  intro E _ _ _ H Dw l Xo c C X₁ φ d m hm hd p _ z₁ t₀ e
  obtain ⟨f, hf0, hf⟩ := hd p z₁ t₀ e
  have hpow : ∀ t : UCTrait X₁ p z₁, ‖t.val (f ^ m)‖ = ‖t.val f‖ ^ m := fun t => by
    rw [UModel.val_eq_valInt, UModel.val_eq_valInt, map_pow]
    push_cast
    exact norm_pow _ _
  have hexp : ∀ t : UCTrait X₁ p z₁, Real.exp (-(t.sc * (((d * m : ℕ) : ℝ) * φ.evalZ t.T.be))) =
      Real.exp (-(t.sc * (d * φ.evalZ t.T.be))) ^ m := fun t => by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine ⟨f ^ m, ?_, fun t => ?_⟩
  · rw [hpow, hf0, hexp]
  · rcases hf t with h1 | ⟨h, hh, h2⟩
    · left
      rw [hpow, hexp]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 m
    · right
      refine ⟨h, hh, ?_⟩
      rw [hpow]
      exact (pow_le_of_le_one (norm_nonneg _) (UModel.norm_val_le t f) (by omega)).trans h2

end GlobalTheory.UPoinc
