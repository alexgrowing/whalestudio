import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLogTeichmullerAcrisEqMuMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdRStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFontaineTEqMulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.PhiXiUnit

variable {l : ℕ} [Fact l.Prime]

theorem phiA_alg (x : Per.Ainf l) :
    phiA l (algebraMap (Per.Ainf l) (Per.Acris l) x) =
      algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l x) :=
  (GlobalTheory.CrisMaps.phiA_extends l).alg x

theorem φA_tm (x : Per.Fl l) : Per.φA l (Per.tm x) = Per.tm x ^ l := by
  rw [← map_pow]
  exact GlobalTheory.RingIface.phiA_teich l x

theorem φA_tm_root (e : Per.Fl l) :
    Per.φA l (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e)) = Per.tm e := by
  rw [φA_tm, ← map_pow, ← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]

theorem φA_xi (e : Per.Fl l) :
    Per.φA l (xi e) = ∑ i ∈ Finset.range l, Per.tm e ^ i := by
  rw [xi, map_sum]
  simp only [map_pow, φA_tm_root]

theorem φA_mu (e : Per.Fl l) : Per.φA l (mu e) = mu e * Per.φA l (xi e) := by
  rw [φA_xi, mu, map_sub, map_one, φA_tm, mul_comm, geom_sum_mul]

theorem φA_xi_sub (e : Per.Fl l) :
    ∃ s : Per.Ainf l, Per.φA l (xi e) - (l : Per.Ainf l) = mu e * s := by
  refine ⟨∑ i ∈ Finset.range l, ∑ j ∈ Finset.range i, Per.tm e ^ j, ?_⟩
  have h : (l : Per.Ainf l) = ∑ i ∈ Finset.range l, (1 : Per.Ainf l) := by simp
  rw [φA_xi, mu, Finset.mul_sum, h, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, geom_sum_mul]

theorem cancel_mu (C : Core l) (x y : Per.Acris l)
    (h : algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) * x =
      algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) * y) : x = y := by
  have he := GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C
  have hU : IsUnit (algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε))) :=
    GlobalTheory.MemLoc.TFil.isUnit_mu he
  apply GlobalTheory.MemLoc.AwayT.acris_injective C
  apply hU.mul_left_cancel
  rw [← map_mul, ← map_mul, h]

theorem exists_unit (C : Core l) : ∃ u : Per.Acris l, IsUnit u ∧
    (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (xi C.ε)) := by
  have he := GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C
  obtain ⟨t, ρ, ht, hρ, htρ⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l C.ε he.1
  have h1 : t = C.t := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l C.ε C.t he.1 C.t_log).1 t ht
  have hφt := GlobalTheory.T.acrisFrobenius_fontaine_t_eq_mul l C
  rw [← h1, htρ, map_mul, phiA_alg, φA_mu, map_mul, mul_assoc, mul_left_comm (l : Per.Acris l)] at hφt
  have h2 := cancel_mu C _ _ hφt
  have hφρ : IsUnit (phiA l ρ) := hρ.map _
  refine ⟨ρ * ↑hφρ.unit⁻¹, hρ.mul (Units.isUnit _), ?_⟩
  rw [← mul_assoc, ← h2, mul_assoc, IsUnit.mul_val_inv, mul_one]

theorem iterate_sub_one (C : Core l) (u : Per.Acris l)
    (hu : (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (xi C.ε))) :
    ∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑(phiA l))^[m] u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ r := by
  set a := algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) with ha_def
  have ha : phiA l a = a * ((l : Per.Acris l) * u) := by
    rw [ha_def, phiA_alg, φA_mu, map_mul, hu]
  have hdvd : ∀ m : ℕ, (l : Per.Acris l) ^ m ∣ (phiA l ^ m) a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [RingHom.coe_pow, Function.iterate_succ_apply, ha, ← RingHom.coe_pow, map_mul, map_mul,
        map_natCast, pow_succ]
      obtain ⟨c, hc⟩ := ih
      rw [hc]
      exact ⟨c * (phiA l ^ m) u, by ring⟩
  obtain ⟨s, hs⟩ := φA_xi_sub C.ε
  have hls : (l : Per.Acris l) * u - l = a * algebraMap (Per.Ainf l) (Per.Acris l) s := by
    rw [hu, ← map_natCast (algebraMap (Per.Ainf l) (Per.Acris l)) l, ← map_sub, hs, map_mul]
  have key : ∀ m : ℕ, (l : Per.Acris l) * ((phiA l ^ m) u - 1) =
      (phiA l ^ m) a * (phiA l ^ m) (algebraMap (Per.Ainf l) (Per.Acris l) s) := by
    intro m
    rw [← map_mul, ← hls, map_sub, map_mul, map_natCast, mul_sub, mul_one]
  have tf := (GlobalTheory.MemLoc.acris_basic l).2.1
  intro r
  refine ⟨r + 1, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [← RingHom.coe_pow]
  obtain ⟨c, hc⟩ := hdvd (k + 1)
  have h3 : (phiA l ^ (k + 1)) u - 1 =
      (l : Per.Acris l) ^ k * (c * (phiA l ^ (k + 1)) (algebraMap (Per.Ainf l) (Per.Acris l) s)) := by
    rw [← sub_eq_zero]
    apply tf
    rw [mul_sub, key, hc, pow_succ]
    ring
  have h4 : (phiA l ^ (k + 1)) u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ k := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, h3]
    exact dvd_mul_right _ _
  exact Ideal.pow_le_pow_right (by omega) h4

end GlobalTheory.MemLoc.PhiXiUnit

theorem GlobalTheory.MemLoc.phi_xi_unit_tendsto : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l),
    ∃ u : Per.Acris l, IsUnit u ∧
      (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (GlobalTheory.MemLoc.xi C.ε)) ∧
      ∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M,
        (⇑(GlobalTheory.MemLoc.phiA l))^[m] u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ r := by
  intro l _ C
  obtain ⟨u, hu, hlu⟩ := GlobalTheory.MemLoc.PhiXiUnit.exists_unit C
  exact ⟨u, hu, hlu, GlobalTheory.MemLoc.PhiXiUnit.iterate_sub_one C u hlu⟩
