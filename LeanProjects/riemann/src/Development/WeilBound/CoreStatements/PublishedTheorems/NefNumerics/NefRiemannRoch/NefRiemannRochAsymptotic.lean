import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFactorialMulEulerCharTwistPowSubLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharH0H1BoundHigherStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefHigherCohomologyGrowth

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.NefRiemannRoch

theorem hdim_twist_nef_pow_le_of_pos (k : Type) [Field k] [Infinite k] (d : ℕ) :
    ∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → ∀ N : LB Y, IsNef k N →
      ∀ (E : Y.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j →
        ∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow N m)) j ≤ C * (d * (m + 1) ^ (d - 1)) := by
  induction d with
  | zero =>
    intro Y _ hY N hN E _ hE j hj
    refine ⟨0, fun m => ?_⟩
    haveI := isNoetherian_of_isProjOver hY
    have hE0 : suppDim E ≤ 0 := by exact_mod_cast hE
    haveI := subsingleton_coh_of_suppDim_le_zero hE0 hj
    rw [hdim_twist_of_suppDim_le_zero k hE0 (isLB_lbPow hN.isLB m), hdim_eq_zero_of_subsingleton]
    exact Nat.zero_le _
  | succ d ih => exact nefTwist_hdim_bound_succ k d ih

theorem abs_factorial_mul_sections_sub_top_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ), topologicalKrullDim X ≤ (d : ℕ) → ∀ L : LB X, IsNef k L → ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℤ) * (lbH0 k (lbPow L m) : ℤ) - topSelfIntersection k L d * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  intro k _ _ X _ hX d hd L hL
  haveI := isNoetherian_of_isProjOver hX
  obtain ⟨_, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hX
  have hLB := hL.isLB
  have hO : suppDim (structureModule X) ≤ ((d : ℕ) : WithBot ℕ∞) := by
    rw [QCoh.suppDim_structureModule]
    exact hd
  obtain ⟨p, hpdeg, hpeval, hpcoeff⟩ := DiffVanish.exists_polynomial_chi (F := structureModule X)
    (A := lbPow L 0) (B := L) (diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) _ hX hO) ℚ
    (isLB_lbPow hLB 0) hLB
  have hb : ∀ n : ℕ, 0 < n → ∃ C : ℕ, ∀ m : ℕ,
      hdim k (twist (structureModule X) (lbPow L m)) n ≤ C * (d * (m + 1) ^ (d - 1)) :=
    fun n hn => hdim_twist_nef_pow_le_of_pos k d X hX L hL (structureModule X) hO n hn
  choose! Cf hCf using hb
  set D : ℕ := d.factorial with hD
  set K : ℕ := ⌈(D : ℚ) * ∑ i ∈ Finset.range d, |p.coeff i|⌉₊ with hK
  refine ⟨K + D * ∑ i ∈ Finset.range d, Cf (i + 1), fun m => ?_⟩
  have hLm := isLB_lbPow hLB m
  haveI : IsFiniteQC (twist (structureModule X) (lbPow L m)) := isFiniteQC_twist hLm
  have hvan : ∀ n : ℕ, d + 1 ≤ n → Subsingleton (coh (twist (structureModule X) (lbPow L m)) n) := by
    intro n hn
    refine IsAmpleLB.subsingleton_coh_of_suppDim_lt hA _ ?_
    rw [suppDim_twist hLm]
    refine lt_of_le_of_lt hO ?_
    exact_mod_cast (Nat.lt_of_succ_le hn)
  have hchi1 := chi_eq_sum_range k (d + 1) hvan
  have hchi2 : (chi k (twist (structureModule X) (lbPow L m)) : ℚ) = p.eval (m : ℚ) := by
    rw [← hpeval (m : ℤ) (lbPow L m) hLm]
    · push_cast
      rfl
    · rw [cls_lbPow hLB, cls_lbPow hLB]
      simp
  have hev := Polynomial.eval_eq_sum_range' (n := d + 1) (by omega) (m : ℚ) (p := p)
  have hcd : (D : ℚ) * p.coeff d = (topSelfIntersection k L d : ℚ) := by
    rw [hpcoeff, topSelf_def]
    have : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos d).ne'
    field_simp
  set h : ℕ → ℚ := fun n => (hdim k (twist (structureModule X) (lbPow L m)) n : ℚ) with hh
  have hB : ∀ i ∈ Finset.range d, ((m : ℚ) ^ i ≤ (d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : (m : ℚ) ^ i ≤ ((m : ℚ) + 1) ^ i := pow_le_pow_left₀ (by positivity) (by linarith) i
    have h2 : ((m : ℚ) + 1) ^ i ≤ ((m : ℚ) + 1) ^ (d - 1) :=
      pow_le_pow_right₀ (by have : (0 : ℚ) ≤ m := by positivity
                            linarith) (by omega)
    have h3 : ((m : ℚ) + 1) ^ (d - 1) ≤ (d : ℚ) * ((m : ℚ) + 1) ^ (d - 1) := by
      have : (1 : ℚ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
      have : (0 : ℚ) ≤ ((m : ℚ) + 1) ^ (d - 1) := by positivity
      nlinarith
    linarith
  have hH : ∀ i ∈ Finset.range d, h (i + 1) ≤ (Cf (i + 1) : ℚ) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
    intro i _
    have := hCf (i + 1) (Nat.succ_pos i) m
    simp only [hh]
    exact_mod_cast this
  have hkey : ((D : ℚ) * h 0 - (topSelfIntersection k L d : ℚ) * (m : ℚ) ^ d) =
      (D : ℚ) * ∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i
        - (D : ℚ) * ∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1) := by
    have e1 : (chi k (twist (structureModule X) (lbPow L m)) : ℚ) =
        h 0 + ∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1) := by
      rw [hchi1]
      push_cast
      rw [Finset.sum_range_succ']
      simp [hh]
      ring
    rw [hchi2, hev, Finset.sum_range_succ] at e1
    linear_combination (-(D : ℚ)) * e1 + (m : ℚ) ^ d * hcd
  have hfin : |(D : ℚ) * h 0 - (topSelfIntersection k L d : ℚ) * (m : ℚ) ^ d| ≤
      ((K + D * ∑ i ∈ Finset.range d, Cf (i + 1) : ℕ) : ℚ) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
    rw [hkey]
    set B : ℚ := (d : ℚ) * ((m : ℚ) + 1) ^ (d - 1) with hBdef
    have hD0 : (0 : ℚ) ≤ D := by positivity
    have s1 : |∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i| ≤ (∑ i ∈ Finset.range d, |p.coeff i|) * B := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (m : ℚ) ^ i)]
      exact mul_le_mul_of_nonneg_left (hB i hi) (abs_nonneg _)
    have s2 : |∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1)| ≤ (∑ i ∈ Finset.range d, (Cf (i + 1) : ℚ)) * B := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (by simp only [hh]; positivity)]
      exact hH i hi
    have hK' : (D : ℚ) * ∑ i ∈ Finset.range d, |p.coeff i| ≤ (K : ℚ) := Nat.le_ceil _
    have hB0 : 0 ≤ B := by positivity
    calc |(D : ℚ) * ∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i
          - (D : ℚ) * ∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1)|
        ≤ |(D : ℚ) * ∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i|
          + |(D : ℚ) * ∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1)| := abs_sub _ _
      _ = (D : ℚ) * |∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i|
          + (D : ℚ) * |∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hD0]
      _ ≤ (D : ℚ) * ((∑ i ∈ Finset.range d, |p.coeff i|) * B)
          + (D : ℚ) * ((∑ i ∈ Finset.range d, (Cf (i + 1) : ℚ)) * B) := by
          gcongr
      _ ≤ (K : ℚ) * B + (D : ℚ) * ((∑ i ∈ Finset.range d, (Cf (i + 1) : ℚ)) * B) := by
          nlinarith
      _ = ((K + D * ∑ i ∈ Finset.range d, Cf (i + 1) : ℕ) : ℚ) * B := by
          push_cast
          ring
  have hfin' : ((|(d.factorial : ℤ) * (lbH0 k (lbPow L m) : ℤ) - topSelfIntersection k L d * (m : ℤ) ^ d| : ℤ) : ℚ) ≤
      (((K + D * ∑ i ∈ Finset.range d, Cf (i + 1) : ℕ) : ℤ) * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) : ℤ) := by
    push_cast
    simpa [hh, lbH0, hD] using hfin
  exact_mod_cast hfin'

end GlobalTheory.NefRiemannRoch
