import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaDeRhamFiltrationAcrisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisPhiPowEigenvectorDoubleSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusDoubleSeriesHasSumAndNormBoundsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLawsStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PSer TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PSer

theorem iterate_phiB_eB_symm (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (j : ℕ) (a : Formalism.Per.Acris l) :
    P.φB^[j] (T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) a)) =
      T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l)
        ((GlobalTheory.MemLoc.phiA l)^[j] a)) := by
  induction j generalizing a with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have h1 : P.φB (T.eB.symm (algebraMap _ (Formalism.Per.Bcris l) a)) =
        T.eB.symm (algebraMap _ (Formalism.Per.Bcris l) (GlobalTheory.MemLoc.phiA l a)) := by
      apply T.eB.injective
      rw [T.frob, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      exact GlobalTheory.CrisMaps.φB_phiA l a
    rw [h1, ih]

theorem iterate_phiB_algebraMap_mul (l : ℕ) [Fact l.Prime] (P : LocPrime l) (c : ℚ_[l]) (j : ℕ)
    (x : P.R.B) : P.φB^[j] (algebraMap ℚ_[l] P.R.B c * x) = algebraMap ℚ_[l] P.R.B c * P.φB^[j] x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, AlgHom.commutes]

theorem series_residues : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧
      (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧
      (∀ c : ℚ_[l], ∃ hm, θ ⟨algebraMap ℚ_[l] P.R.BdR c, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c) ∧
      ∀ (h : ℕ) (r : ℝ) (y : ℕ → Formalism.Per.Fl l), 2 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) →
        ∃ b : P.R.B, Plus T b ∧ P.φB^[h] b = (l : P.R.B) * b ∧
          ∀ j : ℕ, ∃ hm, θ ⟨ev P j b, hm⟩ = abelian₂ h j y := by
  intro l _ P AI T
  obtain ⟨S, θ, Θ, hS, hθ1, hθc, hΘn, hΘt, hΘ⟩ := GlobalTheory.T.exists_theta_deRhamFiltration_acris l P AI T
  refine ⟨S, θ, hS, hθ1, hθc, ?_⟩
  intro h r y hh hr hy
  have hp : l.Prime := Fact.out
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hy 0)
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.ne_zero)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hlpos hr
  have hNle : N ≤ l ^ (h * N) :=
    (Nat.lt_pow_self hp.one_lt).le.trans (Nat.pow_le_pow_right hp.pos (Nat.le_mul_of_pos_left N (by omega)))
  have key : ∀ k, ‖sh (y k ^ l ^ (h * N))‖ ≤ ‖(l : ℂ_[l])‖ := by
    intro k
    rw [(GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l).2.2.2.1, norm_pow]
    calc ‖sh (y k)‖ ^ (l ^ (h * N)) ≤ r ^ (l ^ (h * N)) := pow_le_pow_left₀ (norm_nonneg _) (hy k) _
      _ ≤ r ^ N := pow_le_pow_of_le_one hr0 hr.le hNle
      _ ≤ ‖(l : ℂ_[l])‖ := hN.le
  obtain ⟨w, hwφ, hwΘ⟩ := GlobalTheory.T.exists_acris_phi_pow_eigenvector_double_series l h (fun k => y k ^ l ^ (h * N)) hh key
  set c : ℚ_[l] := ((l : ℚ_[l]) ^ N)⁻¹ with hcdef
  set b' : P.R.B := T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) w) with hb'
  refine ⟨algebraMap ℚ_[l] P.R.B c * b', ?_, ?_, ?_⟩
  · refine ⟨N, w, ?_⟩
    have hc : (l : P.R.B) ^ N * algebraMap ℚ_[l] P.R.B c = 1 := by
      rw [← map_natCast (algebraMap ℚ_[l] P.R.B), ← map_pow, ← map_mul, hcdef,
        mul_inv_cancel₀ (pow_ne_zero _ hl0), map_one]
    rw [← mul_assoc, hc, one_mul, hb', RingEquiv.apply_symm_apply]
  · rw [iterate_phiB_algebraMap_mul, hb', iterate_phiB_eB_symm, hwφ, map_mul, map_natCast, map_mul,
      map_natCast]
    ring
  · intro j
    obtain ⟨hm1, e1⟩ := hθc c
    obtain ⟨hm2, e2⟩ := hΘ ((GlobalTheory.MemLoc.phiA l)^[j] w)
    have heq : ev P j (algebraMap ℚ_[l] P.R.B c * b') = algebraMap ℚ_[l] P.R.BdR c *
        P.ιB (T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l)
          ((GlobalTheory.MemLoc.phiA l)^[j] w))) := by
      rw [ev, iterate_phiB_algebraMap_mul, hb', iterate_phiB_eB_symm, map_mul, AlgHom.commutes]
    refine ⟨heq ▸ S.mul_mem hm1 hm2, ?_⟩
    have hsub : (⟨ev P j (algebraMap ℚ_[l] P.R.B c * b'), heq ▸ S.mul_mem hm1 hm2⟩ : ↥S) =
        ⟨algebraMap ℚ_[l] P.R.BdR c, hm1⟩ * ⟨_, hm2⟩ := Subtype.ext heq
    rw [hsub, map_mul, e1, e2, hwΘ Θ hΘn hΘt j,
      (GlobalTheory.T.untiltFrobeniusDoubleSeries_hasSum_and_norm_bounds l h j r y (by omega) hr hy).2.2.2 N, hcdef, map_inv₀, map_pow, map_natCast,
      inv_mul_cancel_left₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero))]

end GlobalTheory.PSer

end
