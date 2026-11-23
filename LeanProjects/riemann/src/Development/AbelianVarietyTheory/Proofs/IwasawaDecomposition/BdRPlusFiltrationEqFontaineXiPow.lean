import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElementStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfIsDomainAndAinfInvPInjectiveStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.FilPrincipal

section General
variable {R : Type} [CommRing R] {I : Ideal R} {a : R}

theorem evalₐ_eq_zero_iff (h : I = Ideal.span {a}) (n : ℕ) (y : AdicCompletion I R) :
    AdicCompletion.evalₐ I n y = 0 ↔ algebraMap R (AdicCompletion I R) a ^ n ∣ y := by
  have hfg : I.FG := ⟨{a}, by simp [h]⟩
  have e : (I ^ n).map (algebraMap R (AdicCompletion I R)) =
      Ideal.span {algebraMap R (AdicCompletion I R) a ^ n} := by
    have : I ^ n = Ideal.span {a ^ n} := by rw [h, Ideal.span_singleton_pow]
    rw [this, Ideal.map_span, Set.image_singleton, map_pow]
  rw [← Ideal.mem_span_singleton, ← e, ← Submodule.restrictScalars_mem R,
    ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]
  have h' : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  exact map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R h').injective

theorem evalₐ_algebraMap (n : ℕ) (r : R) :
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r) = Ideal.Quotient.mk _ r := by
  rw [AlgHom.commutes]; rfl

theorem evalₐ_surj (n : ℕ) : Function.Surjective (AdicCompletion.evalₐ I n) := by
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨_, evalₐ_algebraMap n r⟩

theorem regular_of_isDomain [IsDomain R] (h : I = Ideal.span {a}) (ha : a ≠ 0) (y : AdicCompletion I R)
    (hy : algebraMap R (AdicCompletion I R) a * y = 0) : y = 0 := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [map_zero, evalₐ_eq_zero_iff h]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
  have h1 : algebraMap R (AdicCompletion I R) a ^ (n + 1) ∣ y - algebraMap R _ r := by
    rw [← evalₐ_eq_zero_iff h, map_sub, evalₐ_algebraMap, hr, sub_self]
  have h2 := congrArg (AdicCompletion.evalₐ I (n + 1)) hy
  rw [map_mul, map_zero, evalₐ_algebraMap, ← hr, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h2
  have h3 : I ^ (n + 1) = Ideal.span {a ^ (n + 1)} := by rw [h, Ideal.span_singleton_pow]
  rw [h3, Ideal.mem_span_singleton, pow_succ', mul_dvd_mul_iff_left ha] at h2
  have h4 : algebraMap R (AdicCompletion I R) a ^ n ∣ algebraMap R _ r := by
    rw [← map_pow]; exact map_dvd _ h2
  have h5 := dvd_add ((pow_dvd_pow _ (Nat.le_succ n)).trans h1) h4
  rwa [sub_add_cancel] at h5

theorem isAdicComplete_span (h : I = Ideal.span {a}) :
    IsAdicComplete (Ideal.span {algebraMap R (AdicCompletion I R) a}) (AdicCompletion I R) := by
  have hfg : I.FG := ⟨{a}, by simp [h]⟩
  have e : I.map (algebraMap R (AdicCompletion I R)) =
      Ideal.span {algebraMap R (AdicCompletion I R) a} := by
    have : ∀ J : Ideal R, J = Ideal.span {a} → J.map (algebraMap R (AdicCompletion I R)) =
        Ideal.span {algebraMap R (AdicCompletion I R) a} := by
      rintro J rfl
      rw [Ideal.map_span, Set.image_singleton]
    exact this I h
  rw [← e, IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete hfg

end General

theorem xi_ne_zero {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (he : IsEps e) : xi e ≠ 0 := by
  intro h0
  set a := (frobeniusEquiv (Per.Fl l) l).symm e with ha
  have h1 : xi e * (Per.tm a - 1) = Per.tm a ^ l - 1 := geom_sum_mul _ _
  rw [h0, zero_mul, eq_comm, sub_eq_zero, ← map_pow] at h1
  have h2 := congrArg (fun w : Per.Ainf l => w.coeff 0) h1
  simp only [WittVector.teichmuller_coeff_zero, WittVector.one_coeff_zero] at h2
  have h3 : a = 1 := by
    apply (frobeniusEquiv (Per.Fl l) l).injective
    rw [frobeniusEquiv_apply, frobenius_def, h2, map_one]
  apply he.2
  rw [← ha, h3, map_one]

end GlobalTheory.MemLoc.FilPrincipal

open GlobalTheory.MemLoc.FilPrincipal in

theorem GlobalTheory.MemLoc.filtration_eq_xi_pow : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e →
    (∀ (n : ℕ) (y : Per.BdRp l), y ∈ Per.FilP l n ↔ aDp l (xi e) ^ n ∣ y) ∧
    (∀ y : Per.BdRp l, aDp l (xi e) * y = 0 → y = 0) ∧
    IsAdicComplete (Ideal.span {aDp l (xi e)}) (Per.BdRp l) ∧
    (∀ n : ℕ, Function.Surjective (Per.ev l n)) := by
  intro l _ e he
  have hk := GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he
  obtain ⟨-, hd, hinj⟩ := GlobalTheory.T.usage l
  have hne : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ≠ 0 := fun h =>
    xi_ne_zero e he (hinj (h.trans (map_zero _).symm))
  obtain ⟨E, hE, hev⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  have ha : E (aDp l (xi e)) = algebraMap (Per.AinfP l) (AdicCompletion (Per.kerP l) (Per.AinfP l))
      (algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)) := by
    rw [aDp, RingHom.comp_apply, hE]
  refine ⟨fun n y => ?_, fun y hy => ?_, ?_, fun n => GlobalTheory.RingIface.ev_surj l n⟩
  · rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, ← hev, evalₐ_eq_zero_iff hk n (E y), ← ha, ← map_pow]
    exact map_dvd_iff E
  · have h1 := congrArg E hy
    rw [map_mul, map_zero, ha] at h1
    exact E.injective ((regular_of_isDomain hk hne (E y) h1).trans (map_zero E).symm)
  · rw [← IsAdicComplete.congr_ringEquiv _ E, Ideal.map_span, Set.image_singleton, ha]
    exact isAdicComplete_span hk
