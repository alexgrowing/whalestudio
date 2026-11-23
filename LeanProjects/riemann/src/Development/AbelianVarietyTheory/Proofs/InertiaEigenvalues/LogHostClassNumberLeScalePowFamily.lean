import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv
import Formalism.SharpRestriction.LevelLetterCocycles.MemPrimesOverOfMem
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.ClassNumHost

theorem totCx (D : D7) : IsTotallyComplex D.host.E := by
  first
  | exact inferInstance
  | (haveI : IsCMField D.host.E := D.host.isCMField_hostE; exact inferInstance)

theorem log_hE_le_rd (D : D7) :
    Real.log (Formalism.MainNotions.N.hE D.host : ℝ) ≤ (D.R.f : ℝ) * Real.log D.host.rdE +
      2 * D.R.f * Real.log (1 + D.R.f * Real.log D.host.rdE) := by
  haveI := totCx D
  have hf := Formalism.MainNotions.TwistedPlaces.finrank_E_host D
  have h := GlobalTheory.log_classNumber_le_log_abs_discr_div D.host.E D.R.f hf
  have hd : 0 < |(discr D.host.E : ℝ)| := by
    have := NumberField.discr_ne_zero D.host.E
    positivity
  have hrd : Real.log D.host.rdE = Real.log |(discr D.host.E : ℝ)| / (2 * D.R.f) := by
    unfold Formalism.BasicNotions.Host.rdE
    rw [Real.log_rpow hd, hf]
    push_cast
    ring
  rw [hrd]
  unfold Formalism.MainNotions.N.hE
  exact h

theorem log_hE_le_lin (D : D7) (h1 : 1 ≤ D.host.rdE) :
    Real.log (Formalism.MainNotions.N.hE D.host : ℝ) ≤ (1 + 2 * D.R.f) * ((D.R.f : ℝ) * Real.log D.host.rdE) := by
  have h := log_hE_le_rd D
  have hY : 0 ≤ (D.R.f : ℝ) * Real.log D.host.rdE := mul_nonneg (by positivity) (Real.log_nonneg h1)
  have hl : Real.log (1 + D.R.f * Real.log D.host.rdE) ≤ D.R.f * Real.log D.host.rdE := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + D.R.f * Real.log D.host.rdE by linarith)
    linarith
  have hf0 : (0:ℝ) ≤ 2 * D.R.f := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hl hf0]

end GlobalTheory.ClassNumHost

namespace GlobalTheory.ClassNumHost

theorem log_rd_le (D : D7) (h1 : 1 ≤ D.host.rdE)
    (h2 : D.host.rdE ≤ (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d)) :
    Real.log D.host.rdE ≤ 2 * D.R.n + (Real.log D.host.q + Real.log D.host.d) / 2 := by
  have hn : (0:ℝ) < D.R.n := by
    have : 0 < D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hqd : (0:ℝ) < (D.host.q : ℝ) * D.host.d := by
    rcases (show (0:ℝ) ≤ (D.host.q : ℝ) * D.host.d by positivity).lt_or_eq with h | h
    · exact h
    · rw [← h, Real.sqrt_zero] at h2; linarith
  have hq : (0:ℝ) < D.host.q := by
    rcases (show (0:ℝ) ≤ D.host.q by positivity).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hqd; exact absurd hqd (lt_irrefl 0)
  have hd : (0:ℝ) < D.host.d := by
    rcases (show (0:ℝ) ≤ D.host.d by positivity).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hqd; exact absurd hqd (lt_irrefl 0)
  have hQ : (D.host.QS : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by exact_mod_cast D.host.QS_le
  have h3 : D.host.rdE ≤ (D.R.n : ℝ) ^ 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) :=
    h2.trans (mul_le_mul_of_nonneg_right (by have : (0:ℝ) ≤ D.host.QS := Nat.cast_nonneg _; linarith) (Real.sqrt_nonneg _))
  have hl := Real.log_le_log (by linarith) h3
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_sqrt hqd.le, Real.log_mul hq.ne' hd.ne'] at hl
  push_cast at hl
  have hn' : Real.log (D.R.n : ℝ) ≤ D.R.n := by
    have := Real.log_le_sub_one_of_pos hn; linarith
  linarith

end GlobalTheory.ClassNumHost

namespace GlobalTheory

theorem log_hE_le_pow : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x →
    ∀ i : Fm.Ix x, Real.log (Formalism.MainNotions.N.hE (Fm.D x i).host : ℝ) ≤ C * x ^ C := by
  intro eps Fm
  set A : ℝ := |2 + 8 * eps + eps / 100| + |eps / 5 + eps / 100| + 1 with hA
  have hA1 : 1 ≤ A := by have := abs_nonneg (2 + 8 * eps + eps / 100); have := abs_nonneg (eps / 5 + eps / 100); linarith
  refine ⟨30 + 3 * A, 1, fun x hx1 hx i => ?_⟩
  have hs := Fm.sizes x hx i
  obtain ⟨hN, -, -, -, -, -, hQD, -⟩ := hs
  have hLx := Fm.L_x x i hx
  have hLe := Fm.L_eps x i
  unfold SizeN szTh at hN
  unfold SizeQD szTh at hQD
  rw [hLx, hLe] at hN hQD
  obtain ⟨-, -, hq, -, hd, -, hr1, hr2⟩ := hQD
  set D := Fm.D x i with hD
  have hx0 : (0:ℝ) < x := by linarith
  have mono : ∀ a : ℝ, a ≤ A → x ^ a ≤ x ^ A := fun a ha => Real.rpow_le_rpow_of_exponent_le hx1 ha
  have hP1 : 1 ≤ x ^ A := Real.one_le_rpow hx1 (by linarith)
  set P := x ^ A with hP
  have hn : (D.R.n : ℝ) ≤ P := hN.2.trans (mono _ (by
    have := le_abs_self (2 + 8 * eps + eps / 100); have := abs_nonneg (eps / 5 + eps / 100); linarith))
  have hqP : Real.log D.host.q ≤ P := hq.trans (mono _ (by
    have := le_abs_self (eps / 5 + eps / 100); have := abs_nonneg (2 + 8 * eps + eps / 100); linarith))
  have hdP : Real.log D.host.d ≤ P := hd.trans (mono _ (by
    have := le_abs_self (eps / 5 + eps / 100); have := abs_nonneg (2 + 8 * eps + eps / 100); linarith))
  have hrd := GlobalTheory.ClassNumHost.log_rd_le D hr1 hr2
  have hrdP : Real.log D.host.rdE ≤ 3 * P := by linarith
  have hrd0 : 0 ≤ Real.log D.host.rdE := Real.log_nonneg hr1
  have hf : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hfP : (D.R.f : ℝ) ≤ 2 * P := by rw [hf]; linarith
  have hf0 : (0:ℝ) ≤ D.R.f := by positivity
  have hmain := GlobalTheory.ClassNumHost.log_hE_le_lin D hr1
  have hY : (D.R.f : ℝ) * Real.log D.host.rdE ≤ 6 * P ^ 2 := by
    calc (D.R.f : ℝ) * Real.log D.host.rdE ≤ (2 * P) * (3 * P) :=
          mul_le_mul hfP hrdP hrd0 (by linarith)
      _ = 6 * P ^ 2 := by ring
  have hY0 : 0 ≤ (D.R.f : ℝ) * Real.log D.host.rdE := mul_nonneg hf0 hrd0
  have h1f : 1 + 2 * (D.R.f : ℝ) ≤ 5 * P := by linarith
  have hbound : Real.log (Formalism.MainNotions.N.hE D.host : ℝ) ≤ 30 * P ^ 3 := by
    calc _ ≤ (1 + 2 * D.R.f) * ((D.R.f : ℝ) * Real.log D.host.rdE) := hmain
      _ ≤ (5 * P) * (6 * P ^ 2) := mul_le_mul h1f hY hY0 (by linarith)
      _ = 30 * P ^ 3 := by ring
  have hP3 : P ^ 3 = x ^ (3 * A) := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  have hxC : x ^ (3 * A) ≤ x ^ (30 + 3 * A) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hx3 : 1 ≤ x ^ (3 * A) := Real.one_le_rpow hx1 (by linarith)
  rw [hP3] at hbound
  calc _ ≤ 30 * x ^ (3 * A) := hbound
    _ ≤ (30 + 3 * A) * x ^ (30 + 3 * A) := by nlinarith

end GlobalTheory
