import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDualExponentialLeOfAinfValuedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExponentialExistsUniqueCyclotomicLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExponentialImageContainsLatticeStatement

noncomputable section

namespace GlobalTheory.Cyc.ExpScalar

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem expStar_mul_sub (LT : LocTheory) (G : Subgroup (GQ l)) (e : ℕ) (c : ℚ_[l])
    {z z' : GQ l → ℚ_[l]} {α α' : Om l} (h : ExpStar LT G e z α) (h' : ExpStar LT G e z' α') :
    ExpStar LT G e (fun σ => c * z σ - z' σ) (algebraMap ℚ_[l] (Om l) c * α - α') := by
  obtain ⟨⟨c1, -, m⟩, b, hb, H⟩ := h
  obtain ⟨⟨c', -, m'⟩, b', hb', H'⟩ := h'
  have hs : ∀ (n : ℤ) (x : (LT l).R.BdR), x ∈ ((LT l).PD (botExt l)).Fil n →
      algebraMap ℚ_[l] (LT l).R.BdR c * x ∈ ((LT l).PD (botExt l)).Fil n := by
    intro n x hx
    have := ((LT l).PD (botExt l)).Fil n |>.smul_mem (algebraMap ℚ_[l] ↥(botExt l).1 c) hx
    rwa [algebraMap_smul, Algebra.smul_def] at this
  refine ⟨⟨(continuousOn_const.mul c1).sub c', fun _ _ => trivial, fun g hg h hh => ?_⟩,
    algebraMap ℚ_[l] (LT l).R.BdR c * b - b', Submodule.sub_mem _ (hs _ _ hb) hb',
    fun σ hσ => ?_⟩
  · simp only [m g hg h hh, m' g hg h hh]; ring
  · have := Submodule.sub_mem _ (hs _ _ (H σ hσ)) (H' σ hσ)
    convert this using 1
    simp only [map_sub, map_mul, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]; ring

theorem exponent_le (s e : ℕ) :
    ((e * (s + 1) + padicValNat l e.factorial + 1 + s : ℕ) : ℝ) + (e : ℝ) / ((l : ℝ) - 1) ≤
      (((((e + 2) * s + padicValNat l e + e / (l - 1) + 1 : ℕ) : ℤ) - betaE l s e : ℤ) : ℝ) := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have h1 : (e : ℝ) / ((l : ℝ) - 1) ≤ ((e / (l - 1) : ℕ) : ℝ) + 1 := by
    have h2 := Nat.lt_floor_add_one ((e : ℝ) / ((l - 1 : ℕ) : ℝ))
    rw [Nat.floor_div_eq_div, Nat.cast_sub (by omega), Nat.cast_one] at h2
    exact h2.le
  generalize e / (l - 1) = q at h1
  rcases e with _ | e
  · have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    simp [betaE]
    linarith
  · have h3 : padicValNat l (e + 1).factorial = padicValNat l (e + 1) + padicValNat l e.factorial := by
      rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
    rw [h3]
    simp only [betaE, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
    generalize padicValNat l (e + 1) = u
    generalize padicValNat l e.factorial = v
    push_cast at h1 ⊢
    linarith

theorem exists_expStar_zero_near : ∀ (D : Formalism.BasicNotions.D7), adm2 D → ArchimedeanSignatureMatching D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (z : GQ l → ℚ_[l]), CocOn (Gj K s) (fun σ y => (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z → (∃ b ∈ ((D.loc l).PD (botExt l)).Fil 0, ∀ σ ∈ Gj K s, ∃ a : Ainf l, algebraMap ℚ_[l] (D.loc l).R.BdR (z σ) - (algebraMap ℚ_[l] (D.loc l).R.BdR (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (D.loc l).actQdR σ b - b) - (D.loc l).ιB ((D.locA l).ιA a) ∈ ((D.loc l).PD (botExt l)).Fil ((e : ℤ) + 1)) → ∃ z' : GQ l → ℚ_[l], ExpStar D.loc (Gj K s) e z' 0 ∧ ∀ σ ∈ Gj K s, ‖z' σ - (l : ℚ_[l]) ^ ((e + 2) * s + padicValNat l e + e / (l - 1) + 1) * z σ‖ ≤ 1 := by
  intro D _ _ l _ K s hs e z hz hb
  obtain ⟨α, hα, hE⟩ := (GlobalTheory.T.dualExponential_existsUnique_cyclotomicLevel D l K s hs e).1 z hz
  have hN := GlobalTheory.T.norm_dualExponential_le_of_ainf_valued D l K s hs e z α hα hE hb
  have hx := exponent_le (l := l) s e
  set a : ℕ := (e + 2) * s + padicValNat l e + e / (l - 1) + 1 with ha
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : Om l) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hnl : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap', Padic.norm_p]
  have hmem : (l : Om l) ^ ((a : ℤ) - betaE l s e) * α ∈ Ks K s :=
    mul_mem (zpow_mem (natCast_mem _ _) _) hα
  have hnorm : ‖(l : Om l) ^ ((a : ℤ) - betaE l s e) * α‖ ≤ 1 := by
    have h1 := hN.trans (Real.rpow_le_rpow_of_exponent_le hl.le hx)
    rw [Real.rpow_intCast] at h1
    rw [norm_mul, norm_zpow, hnl, inv_zpow, inv_mul_le_iff₀ (zpow_pos (by linarith) _), mul_one]
    exact h1
  obtain ⟨z1, hz1, hE1⟩ := GlobalTheory.T.dualExponential_image_contains_lattice D l K s hs e _ hmem hnorm
  refine ⟨fun σ => (l : ℚ_[l]) ^ a * z σ - z1 σ, ?_, fun σ hσ => ?_⟩
  · have := expStar_mul_sub D.loc (Gj K s) e ((l : ℚ_[l]) ^ a) hE hE1
    convert this using 1
    rw [← mul_assoc, ← zpow_add₀ hl0, add_sub_cancel, zpow_natCast, map_pow, map_natCast, sub_self]
  · simpa using hz1 σ hσ

end GlobalTheory.Cyc.ExpScalar
