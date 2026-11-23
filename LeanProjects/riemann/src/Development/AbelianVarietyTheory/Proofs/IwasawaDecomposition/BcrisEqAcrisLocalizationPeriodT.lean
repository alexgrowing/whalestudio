import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddMulDerivativeTrunc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusEigenFilEqQlMulTPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisToBdRPlusInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLogTeichmullerAcrisEqMuMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdRStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerTiltMinusOnePowDivEnvelopeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlusStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.BcrisT

variable {l : ℕ} [Fact l.Prime]

theorem mu_mem_kerP (e : Per.Fl l) (he : e.untilt = 1) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) ∈ Per.kerP l := by
  refine GlobalTheory.RingIface.alg_mem_kerP l ?_
  rw [map_sub, map_one, WittVector.fontaineTheta_teichmuller, he, sub_self]

theorem isLog_mem_fil (e : Per.Fl l) (he : e.untilt = 1) (y : Per.BdRp l) (hy : Per.IsLog l e y) :
    y ∈ Per.FilP l 1 := by
  have h := GlobalTheory.CrisIncl.factorial_mul_ev l e y he hy 1
  rw [Finset.sum_range_one] at h
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_zero, zero_add, Nat.div_one, pow_one] at h
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, h, Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact mu_mem_kerP e he

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem isLog_pow (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j) (e : Per.Fl l) (he : e.untilt = 1)
    (x : Per.BdRp l) (hx : Per.IsLog l e x) (n : ℕ) :
    ∀ y : Per.BdRp l, Per.IsLog l (e ^ n) y → y = (n : Per.BdRp l) * x := by
  induction n with
  | zero =>
    intro y hy
    rw [pow_zero] at hy
    have h1 : (1 : Per.Fl l).untilt = 1 := map_one _
    have h := LogAdd.log_add l 1 1 y y y h1 h1 hy hy (by rwa [mul_one])
    rw [Nat.cast_zero, zero_mul]
    exact left_eq_add.1 h
  | succ n ih =>
    intro y hy
    have hn : (e ^ n).untilt = 1 := by rw [map_pow, he, one_pow]
    obtain ⟨t, u, ht, -, -⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l (e ^ n) hn
    have h1 := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l (e ^ n) t hn ht).2.2.2 j hj
    have h := LogAdd.log_add l (e ^ n) e (j t) x y hn he h1 hx (by rwa [← pow_succ])
    rw [h, ih _ h1, Nat.cast_succ, add_mul, one_mul]

theorem phi_log (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j) (e : Per.Fl l) (he : e.untilt = 1)
    (t : Per.Acris l) (ht : IsLogA e t) : phiA l t = (l : Per.Acris l) ^ 1 * t := by
  have hl : (e ^ l).untilt = 1 := by rw [map_pow, he, one_pow]
  obtain ⟨-, -, h2, h3⟩ := GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l e t he ht
  have h4 := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l (e ^ l) _ hl h2).2.2.2 j hj
  apply GlobalTheory.T.acrisToBdRPlus_injective l j hj
  rw [isLog_pow j hj e he _ (h3 j hj) l _ h4, pow_one, map_mul, map_natCast]

theorem l_dvd (C : Core l) : (l : Per.Acris l) ∣ C.t ^ (l - 1) := by
  have he : C.ε.untilt = 1 := (core_isEps l C).1
  obtain ⟨t, u, ht, -, htu⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l C.ε he
  have e1 : t = C.t := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l C.ε C.t he C.t_log).1 t ht
  obtain ⟨w, hw, -⟩ := GlobalTheory.T.exists_teichmullerTiltMinusOne_pow_div_envelope l C.ε he
  have hw0 : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu C.ε) ^ (l - 1) := by
    apply Subtype.ext
    simpa using hw
  have hw1 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) hw0
  rw [map_mul, map_natCast, map_pow] at hw1
  have e2 : algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu C.ε)) =
      algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) := (GlobalTheory.RingIface.tower l _).symm
  rw [e2] at hw1
  rw [← e1, htu, mul_pow, ← hw1]
  exact (dvd_mul_right _ _).mul_right _

theorem mu_dvd_pt (C : Core l) [Nontrivial (Per.Bcris l)] (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    ∃ r : ℕ, algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1) ∣ C.t ^ r := by
  have hyu := GlobalTheory.CrisLoc.unit_of_root l e he hne
  obtain ⟨t, u, ht, hu, htu⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l e he
  have hlog := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l e t he ht).2.2.2 C.j C.j_cris
  obtain ⟨z, k, hz⟩ := GlobalTheory.T.acris_frobenius_eigen_fil_eq_qlMul_tPow l C 1 t (phi_log C.j C.j_cris e he t ht) (isLog_mem_fil e he _ hlog)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero, zero_mul, htu] at hz
    have h := congrArg (algebraMap (Per.Acris l) (Per.Bcris l)) hz
    rw [map_zero, map_mul, map_mul, map_pow, map_natCast] at h
    have hU : IsUnit (0 : Per.Bcris l) := by
      rw [← h]
      exact ((GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C).2.2.2.pow k).mul (hyu.mul (hu.map _))
    exact not_isUnit_zero hU
  have hs := congrArg ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l)) (PadicInt.unitCoeff_spec hz0)
  rw [map_mul, map_pow, map_natCast] at hs
  have hU := (PadicInt.unitCoeff hz0).isUnit.map ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l))
  have h1 : algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ∣
      ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l)) z * C.t ^ 1 := by
    rw [RingHom.comp_apply, ← hz, htu]
    exact (dvd_mul_right _ _).mul_left _
  rw [hs, mul_assoc, hU.dvd_mul_left] at h1
  refine ⟨(l - 1) * z.valuation + 1, h1.trans ?_⟩
  rw [pow_add, pow_mul]
  exact mul_dvd_mul_right (pow_dvd_pow_of_dvd (l_dvd C) _) _

theorem away_pt (C : Core l) [Nontrivial (Per.Bcris l)] (b : Per.Bcris l) :
    ∃ (r : ℕ) (x : Per.Acris l),
      b * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ r = algebraMap (Per.Acris l) (Per.Bcris l) x := by
  obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  obtain ⟨n, x, hx⟩ := GlobalTheory.CrisLoc.exists_mul_pow_eq l e he hne b
  obtain ⟨r, c, hc⟩ := mu_dvd_pt C e he hne
  refine ⟨r * n, x * c ^ n, ?_⟩
  rw [← map_pow, pow_mul, hc, mul_pow, map_mul, map_mul, map_pow, ← mul_assoc, hx]

end GlobalTheory.MemLoc.BcrisT

namespace GlobalTheory.MemLoc

theorem bcris_eq_acris_localization_periodT_alt (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.Bcris l) :
    ∃ (r : ℕ) (x : Per.Acris l),
      b * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ r = algebraMap (Per.Acris l) (Per.Bcris l) x := by
  rcases subsingleton_or_nontrivial (Per.Bcris l) with h | h
  · exact ⟨0, 0, Subsingleton.elim _ _⟩
  exact BcrisT.away_pt C b

end GlobalTheory.MemLoc
