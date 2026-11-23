import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeRhamFiltrationIffXiPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TiedUnif

theorem zpow_form {R : Type} [CommRing R] (u : Rˣ) (a : ℤ) (x w : R) :
    x * (u : R) ^ (-a).toNat = (u : R) ^ a.toNat * w ↔ x = ((u ^ a : Rˣ) : R) * w := by
  rcases le_total 0 a with h | h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat h
    simp only [neg_neg, Int.toNat_natCast, Int.toNat_neg_natCast, pow_zero, one_mul, zpow_neg,
      zpow_natCast]
    rw [Units.eq_inv_mul_iff_mul_eq, Units.val_pow_eq_pow_val, mul_comm]

variable {l : ℕ} [Fact l.Prime]

def piOne (e : Per.Fl l) : Per.Ainf l := Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) - 1

theorem mu_eq (e : Per.Fl l) : mu e = xi e * piOne e := by
  have h : (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e)) ^ l = Per.tm e := by
    rw [← map_pow, frobeniusEquiv_symm_pow_p]
  rw [mu, piOne, xi, geom_sum_mul, h]

theorem theta_piOne {e : Per.Fl l} (he : IsEps e) : Per.θD l (aDp l (piOne e)) ≠ 0 := by
  rw [(thetaD_props l).2.2.2.1]
  intro h
  apply he.2
  have h' : Per.θ l (piOne e) = 0 := Subtype.ext h
  rw [piOne, map_sub, map_one, WittVector.fontaineTheta_teichmuller, sub_eq_zero] at h'
  exact h'

theorem theta_xi {e : Per.Fl l} (he : IsEps e) : Per.θD l (aDp l (xi e)) = 0 := by
  rw [(thetaD_props l).2.2.2.1, (theta_eq_zero_iff_xi_dvd l e he _).2 dvd_rfl]
  rfl

theorem ev_aDp (n : ℕ) (a : Per.Ainf l) :
    Per.ev l n (aDp l a) = Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a) := by
  rw [aDp, RingHom.comp_apply, GlobalTheory.RingIface.ev_alg]

theorem mem_filtration_iff_eval_eq_zero' {e : Per.Fl l} (he : IsEps e) (n : ℕ) (y : Per.BdRp l) :
    y ∈ Per.FilP l n ↔ Per.ev l n y = 0 := by
  obtain ⟨E, hE, hev⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  rw [(filtration_eq_xi_pow l e he).1, ← hev, FilPrincipal.evalₐ_eq_zero_iff (GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he), ← hE,
    ← map_pow E, map_dvd_iff E, aDp, RingHom.comp_apply]

theorem mu_sub_log {e : Per.Fl l} (he : IsEps e) {y : Per.BdRp l} (hy : Per.IsLog l e y) :
    aDp l (mu e) - y ∈ Per.FilP l 2 := by
  have h2 := GlobalTheory.CrisIncl.factorial_mul_ev l e y he.1 hy 2
  have hsq : Per.ev l 2 (aDp l (mu e ^ 2)) = 0 := by
    refine (mem_filtration_iff_eval_eq_zero' he 2 _).1 (((filtration_eq_xi_pow l e he).1 2 _).2 ?_)
    rw [mu_eq, map_pow, map_mul, mul_pow]
    exact dvd_mul_right _ _
  rw [ev_aDp, map_pow, map_pow] at hsq
  have hu : IsUnit (((2 : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ 2)) := by
    have := (GlobalTheory.RingBasics.isUnit_nat l 2 two_ne_zero).map (Ideal.Quotient.mk (Per.kerP l ^ 2))
    rwa [map_natCast] at this
  rw [mem_filtration_iff_eval_eq_zero' he, map_sub, ev_aDp, sub_eq_zero]
  apply hu.mul_left_cancel
  have hf : Nat.factorial 2 = 2 := rfl
  rw [hf] at h2
  rw [h2]
  change _ = Ideal.Quotient.mk _ (∑ k ∈ Finset.range 2, (-1) ^ k * ((2 / (k + 1) : ℕ) : Per.AinfP l) *
      (algebraMap (Per.Ainf l) (Per.AinfP l) (mu e)) ^ (k + 1))
  rw [Finset.sum_range_succ, Finset.sum_range_one, map_add, map_mul _ _ (_ ^ (1 + 1)), map_pow _ _ (1 + 1),
    show (1 + 1 : ℕ) = 2 from rfl, hsq]
  simp [map_ofNat]

theorem log_eq_xi_mul {e : Per.Fl l} (he : IsEps e) {y : Per.BdRp l} (hy : Per.IsLog l e y) :
    ∃ v : Per.BdRp l, IsUnit v ∧ y = aDp l (xi e) * v := by
  obtain ⟨w, hw⟩ := ((filtration_eq_xi_pow l e he).1 2 _).1 (mu_sub_log he hy)
  refine ⟨aDp l (piOne e) - aDp l (xi e) * w, (thetaD_props l).2.2.1 _ ?_, ?_⟩
  · rw [map_sub, map_mul, theta_xi he, zero_mul, sub_zero]
    exact theta_piOne he
  · rw [mu_eq, map_mul] at hw
    linear_combination -hw

theorem isUnit_xi {e : Per.Fl l} (he : IsEps e) :
    IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e))) := by
  obtain ⟨hd, hinj, hF, -⟩ := BdRField.bdR_isField l
  have h0 : algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ≠ 0 := by
    intro h
    have h1 : aDp l (xi e) = 0 := hinj (by rw [h, map_zero])
    exact one_ne_zero ((filtration_eq_xi_pow l e he).2.1 1 (by rw [h1, zero_mul]))
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel h0
  exact IsUnit.of_mul_eq_one b hb

theorem mem_FilD_iff {e : Per.Fl l} (he : IsEps e) (a : ℤ) (x : Per.BdR l) :
    x ∈ Per.FilD l a ↔ ∃ w : Per.BdRp l,
      x = (((isUnit_xi he).unit ^ a : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w := by
  rw [mem_FilD_iff_xi_pow l e he]
  refine exists_congr fun w => ?_
  rw [← zpow_form, IsUnit.unit_spec, map_mul, map_pow]

theorem filD_succ {e : Per.Fl l} (he : IsEps e) {y : Per.BdRp l} (hy : Per.IsLog l e y) (a : ℤ)
    (x : Per.BdR l) : x ∈ Per.FilD l (a + 1) ↔
      ∃ z ∈ Per.FilD l a, x = algebraMap (Per.BdRp l) (Per.BdR l) y * z := by
  obtain ⟨v, hv, rfl⟩ := log_eq_xi_mul he hy
  obtain ⟨v', hv'⟩ := hv.exists_right_inv
  have hv2 := congrArg (algebraMap (Per.BdRp l) (Per.BdR l)) hv'
  rw [map_mul, map_one] at hv2
  rw [mem_FilD_iff he, zpow_add_one, Units.val_mul, IsUnit.unit_spec, map_mul]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨_, (mem_FilD_iff he a _).2 ⟨v' * w, rfl⟩, ?_⟩
    rw [map_mul]
    linear_combination (-((((isUnit_xi he).unit ^ a : (Per.BdR l)ˣ) : Per.BdR l) *
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) * algebraMap (Per.BdRp l) (Per.BdR l) w)) * hv2
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, rfl⟩ := (mem_FilD_iff he a _).1 hz
    exact ⟨v * w, by rw [map_mul]; ring⟩

theorem alg_mem_FilD (n : ℕ) {z : Per.BdRp l} (hz : z ∈ Per.FilP l n) :
    algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l n :=
  GlobalTheory.RingIface.alg_mem_FilD_nat l hz

theorem exists_isEps_pt (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, h⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  refine ⟨ε, ?_, fun hh => h1 ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← h 1, map_one]
    exact congrArg Subtype.val hh

theorem alg_mem_FilD_zero (z : Per.BdRp l) :
    algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l 0 := by
  obtain ⟨e, he⟩ := exists_isEps_pt l
  exact alg_mem_FilD 0 (((filtration_eq_xi_pow l e he).1 0 z).2 (by rw [pow_zero]; exact one_dvd z))

theorem eD_ιA {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (a : Ainf l) :
    T.eD (P.ιB (AI.ιA a)) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
  have h := GlobalTheory.CrisIncl.incl_aB l _ T.incl a
  rw [← T.ιA] at h
  have h2 : T.eD (P.ιB (T.eB.symm (T.eB (AI.ιA a)))) = _ := h
  rw [RingEquiv.symm_apply_apply] at h2
  exact h2

theorem tied_uniformiser : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ K : FinExt l, P.ιB (AI.ιA AI.μ) - P.ιB P.tB ∈ (P.PD K).Fil 2) ∧ (∀ K : FinExt l, ∃ u ∈ (P.PD K).Fil 0, P.ιB (AI.ιA AI.π₁) * u = 1) ∧ ∀ (K : FinExt l) (a : ℤ) (x : P.R.BdR), x ∈ (P.PD K).Fil (a + 1) ↔ ∃ y ∈ (P.PD K).Fil a, x = P.ιB P.tB * y := by
  intro l _ P AI T
  obtain ⟨C, hC⟩ := FitsEx.exists_fits l P AI T
  have he : IsEps AI.ε := hC.ε ▸ core_isEps l C
  obtain ⟨y, hy, ht⟩ := T.t
  refine ⟨fun K => ?_, fun K => ?_, fun K a x => ?_⟩
  · rw [T.fil, map_sub, eD_ιA T, ht, ← map_sub]
    exact alg_mem_FilD 2 (mu_sub_log he hy)
  · obtain ⟨v, hv⟩ := ((thetaD_props l).2.2.1 _ (theta_piOne he)).exists_right_inv
    refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) v), ?_, T.eD.injective ?_⟩
    · rw [T.fil, RingEquiv.apply_symm_apply]
      exact alg_mem_FilD_zero v
    · rw [map_mul, RingEquiv.apply_symm_apply, eD_ιA T, ← map_mul, map_one]
      exact (congrArg _ hv).trans (map_one _)
  · rw [T.fil, filD_succ he hy]
    constructor
    · rintro ⟨z, hz, e⟩
      refine ⟨T.eD.symm z, ?_, T.eD.injective ?_⟩
      · rwa [T.fil, RingEquiv.apply_symm_apply]
      · rw [map_mul, RingEquiv.apply_symm_apply, ht, e]
    · rintro ⟨z, hz, rfl⟩
      exact ⟨T.eD z, (T.fil K a z).1 hz, by rw [map_mul, ht]⟩

end GlobalTheory.MemLoc.TiedUnif
