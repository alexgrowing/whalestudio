import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.UnitFil

theorem isUnit_of_congr_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S) (B : Matrix (Fin d) (Fin d) (Per.BdRp l)), (∀ i j, bk.E ∣ (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) → (∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l 1) → IsUnit B := by
  intro l _ K bk d k β B h1 h2
  obtain ⟨-, hker, hunit, haD, -⟩ := GlobalTheory.MemLoc.thetaD_props l
  have hE : Per.θ l (bk.ev bk.E) = 0 := by
    have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
    exact this
  have hl0 : ((l : ℂ_[l]) ^ k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hB : ∀ i j, Per.θD l (B i j) = (1 : Matrix (Fin d) (Fin d) ℂ_[l]) i j := by
    intro i j
    have ha := (hker _).2 (h2 i j)
    obtain ⟨c, hc⟩ := h1 i j
    have hb : bk.ev (β i j) = (l : Ainf l) ^ k * bk.ev ((1 : Matrix (Fin d) (Fin d) bk.S) i j) + bk.ev bk.E * bk.ev c := by
      have : β i j = (l : bk.S) ^ k * (1 : Matrix (Fin d) (Fin d) bk.S) i j + bk.E * c := by
        rw [← hc]; simp [Matrix.sub_apply, Matrix.smul_apply]
      rw [this, map_add, map_mul, map_mul, map_pow, map_natCast]
    rw [map_sub, haD, hb, map_add, map_mul, map_mul, hE, zero_mul, add_zero, map_mul] at ha
    simp only [map_pow, map_natCast] at ha
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq, map_one, mul_one] at ha ⊢
      have ha' : ((l : ℂ_[l]) ^ k) * Per.θD l (B i i) = (l : ℂ_[l]) ^ k * 1 := by
        rw [mul_one]; push_cast at ha; linear_combination -ha
      exact mul_left_cancel₀ hl0 ha'
    · simp only [Matrix.one_apply_ne hij, map_zero, mul_zero] at ha ⊢
      push_cast at ha
      have ha' : ((l : ℂ_[l]) ^ k) * Per.θD l (B i j) = 0 := by linear_combination -ha
      exact (mul_eq_zero.1 ha').resolve_left hl0
  have hmap : B.map (Per.θD l) = 1 := Matrix.ext hB
  rw [Matrix.isUnit_iff_isUnit_det]
  apply hunit
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_one]
  exact one_ne_zero

end GlobalTheory.BKLim.UnitFil
