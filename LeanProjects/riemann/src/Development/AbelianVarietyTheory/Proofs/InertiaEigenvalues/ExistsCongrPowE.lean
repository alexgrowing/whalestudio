import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassDivisionClosedDiscBreuilKisin
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.WApprox

theorem ρ₀_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  exact NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by simp only [neg_neg_iff_pos]; positivity)

theorem exists_congr_pow_E : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ) (x : bk.DS bk.ρ₀),
    ∃ (k : ℕ) (s : bk.S), toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m ∣
      (l : bk.DS bk.ρ₀) ^ k * x - toDisc l (X : bk.S) bk.ρ₀ s := by
  intro l _ K bk m
  induction m with
  | zero => intro x; exact ⟨0, 0, by simp⟩
  | succ m ih =>
    intro x
    obtain ⟨q, k, r, -, hx⟩ := WDiv.weierstrass_div l K bk bk.ρ₀ le_rfl (ρ₀_lt_one bk) x
    obtain ⟨k', s', w, hw⟩ := ih q
    refine ⟨k + k', bk.E * s' + (l : bk.S) ^ k' * (r : bk.S), w, ?_⟩
    have hq : (l : bk.DS bk.ρ₀) ^ k' * q = toDisc l (X : bk.S) bk.ρ₀ s' +
        toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m * w := by rw [← hw]; ring
    calc (l : bk.DS bk.ρ₀) ^ (k + k') * x - toDisc l (X : bk.S) bk.ρ₀ (bk.E * s' + (l : bk.S) ^ k' * (r : bk.S))
        = (l : bk.DS bk.ρ₀) ^ k' * ((l : bk.DS bk.ρ₀) ^ k * x) - toDisc l (X : bk.S) bk.ρ₀ (bk.E * s' + (l : bk.S) ^ k' * (r : bk.S)) := by ring
      _ = toDisc l (X : bk.S) bk.ρ₀ bk.E * ((l : bk.DS bk.ρ₀) ^ k' * q) - toDisc l (X : bk.S) bk.ρ₀ bk.E * toDisc l (X : bk.S) bk.ρ₀ s' := by
          rw [hx, map_add, map_mul, map_mul, map_pow, map_natCast]; ring
      _ = toDisc l (X : bk.S) bk.ρ₀ bk.E ^ (m + 1) * w := by rw [hq]; ring

end GlobalTheory.BKLim.WApprox
