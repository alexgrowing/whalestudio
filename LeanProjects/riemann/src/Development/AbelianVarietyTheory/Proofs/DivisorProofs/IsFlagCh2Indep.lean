import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFlagCh2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagCh2EqOfAdjacent
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory

theorem isFlagCh2_indep : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], (∀ (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsIntegral Y], IsArithVar q 1 → Nonempty (RegCover q)) → IsArithVar p 1 → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl fl' : Vert.Flag E r) (a b : ℝ), VMetric.IsFlagCh2 H fl a → VMetric.IsFlagCh2 H fl' b → a = b := by
  intro hA k _ X p _ hR hX E r h H fl fl' a b ha hb
  obtain ⟨C, m, g, h₀, h₁, hg⟩ := GlobalTheory.FlagChain.exists_chain hA k X p hR hX E r h H fl fl'
  have key : ∀ j : Fin (m + 1), VMetric.IsFlagCh2 (H.pull C.ρ rfl) (g j) (C.deg * a) := by
    intro j
    induction j using Fin.induction with
    | zero => exact (h₀ a).1 ha
    | succ j ih =>
      obtain ⟨c, hc⟩ := GlobalTheory.VMetric.exists_isFlagCh2 hA k C.Y (C.ρ ≫ p) C.reg _ r _ (H.pull C.ρ rfl) (g j.succ)
      rwa [GlobalTheory.AdjFlag.isFlagCh2_eq_of_adjacent hA k C.Y (C.ρ ≫ p) C.reg _ r _ (H.pull C.ρ rfl) _ _ (hg j) _ _ ih hc]
  have e := (key (Fin.last m)).unique C.reg.toIsArithVar ((h₁ b).1 hb)
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 C.deg_pos.ne') e

end GlobalTheory
