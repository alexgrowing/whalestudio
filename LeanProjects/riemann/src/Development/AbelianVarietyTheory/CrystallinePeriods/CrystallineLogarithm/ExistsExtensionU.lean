import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Embedding
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.PadicField
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Action
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.MapEqPadicPowCyclotomicCharacter
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Period
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.CrisTheta
namespace CrisHomExtUnit
section
universe u

theorem Bridge.CrisLoc.bcris_hom_ext_u : ∀ (l : ℕ) [Fact l.Prime] {R : Type u} [CommRing R] {f g : (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l)) →+* R} (h : ∀ x : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)), f (algebraMap _ _ x) = g (algebraMap _ _ x)), f = g := by
  intro l _ R _ f g h
  refine Reformulated.AutPerF.Bcris.hom_ext fun y => ?_
  refine RingHom.congr_fun (Reformulated.AutPerF.BcrisPlus.hom_ext
    (f := f.comp (algebraMap (Reformulated.AutPerF.BcrisPlus l ↥(PadicComplexInt l)) _))
    (g := g.comp (algebraMap (Reformulated.AutPerF.BcrisPlus l ↥(PadicComplexInt l)) _)) fun x => ?_) y
  rw [RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  exact h x

end
end CrisHomExtUnit
namespace CrisExtensionUnit
section
universe u

namespace Bridge.CrisLoc.CrisExtensionUnitLemmas

open Ideal Reformulated.AutPerF

theorem geom_eq {A : Type*} [CommRing A] (p : ℕ) (v : A) :
    ∃ c : A, ∑ i ∈ Finset.range p, v ^ i = p + (v - 1) * c := by
  induction p with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow v 1 n
    refine ⟨c + d, ?_⟩
    rw [Finset.sum_range_succ, hc]
    rw [one_pow] at hd
    push_cast
    linear_combination hd

theorem step {A : Type*} [CommRing A] (p n : ℕ) (v w : A)
    (h : v ^ p ^ (n + 1) - 1 = (p : A) ^ (n + 1) * ((v - 1) * w)) :
    ∃ z : A, v ^ p ^ (n + 1 + 1) - 1 =
      (p : A) ^ (n + 1 + 1) * ((v - 1) * (w + (p : A) ^ n * ((v - 1) * z))) := by
  obtain ⟨c, hc⟩ := geom_eq p (v ^ p ^ (n + 1))
  refine ⟨w * w * c, ?_⟩
  rw [pow_succ p (n + 1), pow_mul, ← geom_sum_mul, hc, h]
  ring

theorem key {A : Type*} [CommRing A] (p : ℕ) [IsAdicComplete (span {(p : A)}) A] (v r t : A)
    (h0 : v ^ p - 1 = p * ((v - 1) * r)) (hr : r - 1 ∈ jacobson (⊥ : Ideal A))
    (hv : v - 1 ∈ jacobson (⊥ : Ideal A))
    (ht : ∀ (n : ℕ) (w : A), v ^ p ^ n - 1 = (p : A) ^ n * w → (p : A) ^ n ∣ t - w) :
    ∃ L : A, IsUnit L ∧ t = (v - 1) * L := by
  choose z hz using fun n w h => step p n v w h
  let f : (n : ℕ) → {w : A // v ^ p ^ (n + 1) - 1 = (p : A) ^ (n + 1) * ((v - 1) * w)} :=
    fun n => Nat.rec ⟨r, by simpa using h0⟩
      (fun n w => ⟨w.1 + (p : A) ^ n * ((v - 1) * z n w.1 w.2), hz n w.1 w.2⟩) n
  have hf0 : (f 0).1 = r := rfl
  have hf : ∀ n, (f (n + 1)).1 = (f n).1 + (p : A) ^ n * ((v - 1) * z n (f n).1 (f n).2) :=
    fun n => rfl
  have hmem : ∀ (n : ℕ) (x : A),
      x ∈ (span {(p : A)} ^ n • ⊤ : Submodule A A) ↔ (p : A) ^ n ∣ x := fun n x => by
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := span {(p : A)}) (M := A) inferInstance
    (f := fun n => (f n).1) (by
      intro m n hle
      rw [SModEq.sub_mem, hmem]
      induction n, hle using Nat.le_induction with
      | base => simp
      | succ n hle ih =>
        rw [hf, ← sub_sub]
        exact dvd_sub ih ((pow_dvd_pow _ hle).mul_right _))
  simp only [SModEq.sub_mem, hmem] at hL
  refine ⟨L, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hL 1
    have hp : (p : A) ∈ jacobson (⊥ : Ideal A) :=
      IsAdicComplete.le_jacobson_bot (span {(p : A)}) (mem_span_singleton_self _)
    have hL1 : L - 1 ∈ jacobson (⊥ : Ideal A) := by
      have : L - 1 = (r - 1) + (v - 1) * z 0 (f 0).1 (f 0).2 - p * y := by
        have h1 : (f 1).1 = (f 0).1 + (p : A) ^ 0 * ((v - 1) * z 0 (f 0).1 (f 0).2) := hf 0
        linear_combination hf0 - hy + h1
      rw [this]
      exact sub_mem (add_mem hr (mul_mem_right _ _ hv)) (mul_mem_right _ _ hp)
    simpa using Ideal.mem_jacobson_bot.1 hL1 1
  · rw [← sub_eq_zero]
    refine IsHausdorff.haus (I := span {(p : A)}) inferInstance _ fun n => ?_
    rw [SModEq.zero, hmem]
    have h1 := (pow_dvd_pow _ n.le_succ).trans (ht (n + 1) _ (f n).2)
    have h2 := (hL n).mul_left (v - 1)
    convert dvd_add h1 h2 using 1
    ring

variable {p : ℕ} [Fact p.Prime]
variable {R : Type*} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

theorem p_dvd_pow {y : AcrisZero p R} (hy : y ∈ AcrisZero.pdIdeal p R) :
    (p : Acris p R) ∣ algebraMap (AcrisZero p R) (Acris p R) y ^ p := by
  have h := map_dvd (algebraMap (AcrisZero p R) (Acris p R))
    (AcrisZero.factorial_dvd_pow_of_mem_pdIdeal hy p)
  rw [map_natCast, map_pow] at h
  exact (Nat.cast_dvd_cast (Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl)).trans h

theorem mem_jac {y : AcrisZero p R} (hy : y ∈ AcrisZero.pdIdeal p R) :
    algebraMap (AcrisZero p R) (Acris p R) y ∈ jacobson (⊥ : Ideal (Acris p R)) := by
  refine Ideal.isRadical_jacobson _ ⟨p, ?_⟩
  exact IsAdicComplete.le_jacobson_bot (span {(p : Acris p R)})
    (Ideal.mem_span_singleton.2 (p_dvd_pow hy))

theorem p_dvd_geom [IsDomain R] (e : Tilt p R) (he : PreTilt.untilt e = 1) :
    (p : AcrisZero p R) ∣ algebraMap (Ainf p R) (AcrisZero p R)
      (∑ i ∈ Finset.range p, Ainf.teich p e ^ i) := by
  obtain ⟨e', rfl⟩ : ∃ e' : Tilt p R, e' ^ p = e :=
    ⟨_, frobeniusEquiv_symm_pow_p (Tilt p R) p e⟩
  have hφ : Ainf.frob p R (Ainf.teich p e') = Ainf.teich p (e' ^ p) := by
    rw [Ainf.frob_teich, map_pow]
  by_cases h : PreTilt.untilt e' = 1
  · obtain ⟨c, hc⟩ := geom_eq p (Ainf.teich p (e' ^ p))
    have h1 := AcrisZero.p_dvd_frob (Ainf.teich p e' - 1)
      (by rw [map_sub, Ainf.theta_teich, h, map_one, sub_self])
    rw [map_sub (Ainf.frob p R), hφ, map_one] at h1
    rw [hc, map_add, map_natCast, map_mul]
    exact dvd_add dvd_rfl (h1.mul_right _)
  · have h1 := AcrisZero.p_dvd_frob (∑ i ∈ Finset.range p, Ainf.teich p e' ^ i) (by
      simp only [map_sum, map_pow, Ainf.theta_teich]
      have := geom_sum_mul (PreTilt.untilt e') p
      rw [← map_pow, he, sub_self] at this
      exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 h))
    rw [map_sum (Ainf.frob p R)] at h1
    simp only [map_pow (Ainf.frob p R), hφ] at h1
    exact h1

theorem log_eq [IsDomain R] [CharZero R] (η : tateModule p R) :
    ∃ L : Acris p R, IsUnit L ∧ Acris.logTeich η =
      algebraMap (Ainf p R) (Acris p R) (Ainf.teich p η.1 - 1) * L := by
  have he : PreTilt.untilt η.1 = 1 := η.2
  have hθ : Ainf.theta p R (Ainf.teich p η.1) = 1 := by rw [Ainf.theta_teich, he]
  obtain ⟨r, hr⟩ := p_dvd_geom η.1 he
  have hr1 : r - 1 ∈ AcrisZero.pdIdeal p R := by
    rw [← AcrisZero.theta_eq_zero_iff, map_sub, map_one, sub_eq_zero]
    have h := congrArg (AcrisZero.theta p R) hr
    rw [AcrisZero.theta_algebraMap, map_mul, map_natCast, map_sum] at h
    simp only [map_pow, hθ, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    exact (mul_left_cancel₀ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h).symm
  have hv : algebraMap (Ainf p R) (AcrisZero p R) (Ainf.teich p η.1 - 1) ∈
      AcrisZero.pdIdeal p R :=
    AcrisZero.algebraMap_mem_pdIdeal _ (by rw [map_sub, hθ, map_one, sub_self])
  rw [map_sub, map_one]
  refine key p (algebraMap (Ainf p R) (Acris p R) (Ainf.teich p η.1))
    (algebraMap (AcrisZero p R) (Acris p R) r) _ ?_ ?_ ?_ ?_
  · have h := congrArg (algebraMap (AcrisZero p R) (Acris p R)) hr
    rw [← IsScalarTower.algebraMap_apply, map_mul, map_natCast, map_sum] at h
    simp only [map_pow] at h
    rw [← geom_sum_mul, h]
    ring
  · simpa using mem_jac hr1
  · have h := mem_jac hv
    rwa [← IsScalarTower.algebraMap_apply, map_sub, map_one] at h
  · intro n w hw
    obtain ⟨l, hl, hl'⟩ := Acris.exists_quot (Ainf.teich p η.1) hθ n
    have h := congrArg (algebraMap (AcrisZero p R) (Acris p R)) hl
    rw [map_mul, map_pow, map_natCast, map_sub, map_pow, map_one,
      ← IsScalarTower.algebraMap_apply, hw] at h
    rw [← Acris.p_pow_mul_cancel n h, ← Acris.eval_eq_zero_iff, map_sub, Acris.eval_algebraMap,
      sub_eq_zero]
    exact hl'

theorem main [IsDomain R] [CharZero R] (η : tateModule p R) {B : Type*} [CommRing B]
    (g : Acris p R →+* B)
    (hg : IsUnit (g (algebraMap (Ainf p R) (Acris p R) (Ainf.teich p η.1 - 1)))) :
    ∃ F : Bcris p R →+* B, ∀ x : Acris p R, F (algebraMap _ _ x) = g x := by
  have he : PreTilt.untilt η.1 = 1 := η.2
  have hp : IsUnit (p : B) := by
    have h := map_dvd g (p_dvd_pow (AcrisZero.algebraMap_mem_pdIdeal (Ainf.teich p η.1 - 1)
      (by rw [map_sub, Ainf.theta_teich, he, map_one, sub_self])))
    rw [← IsScalarTower.algebraMap_apply, map_natCast, map_pow] at h
    exact isUnit_of_dvd_unit h (hg.pow _)
  have ht : IsUnit (g (Acris.logTeich η)) := by
    obtain ⟨L, hL, h⟩ := log_eq η
    rw [h, map_mul]
    exact hg.mul (hL.map g)
  refine ⟨Bcris.lift (BcrisPlus.lift g hp) (fun ε hε => ?_), fun x => ?_⟩
  · rw [BcrisPlus.lift_algebraMap]
    obtain ⟨a, rfl⟩ := hε.padicPow_surjective η
    rw [Acris.logTeich_padicPow, map_mul] at ht
    exact isUnit_of_mul_isUnit_right ht
  · rw [IsScalarTower.algebraMap_apply (Acris p R) (BcrisPlus p R) (Bcris p R),
      Bcris.lift_algebraMap, BcrisPlus.lift_algebraMap]

end Bridge.CrisLoc.CrisExtensionUnitLemmas

theorem Bridge.CrisLoc.exists_extension_u : ∀ (l : ℕ) [Fact l.Prime] (e : (Reformulated.AutPerF.Tilt l ↥(PadicComplexInt l))) (he : e.untilt = 1) (hne : e ≠ 1) {R : Type u} [CommRing R] (g : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)) →+* R) (hg : IsUnit (g (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) (WittVector.teichmuller l e - 1)))), ∃ F : (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l)) →+* R, ∀ x : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)), F (algebraMap _ _ x) = g x := by
  intro l _ e he _ R _ g hg
  exact Bridge.CrisLoc.CrisExtensionUnitLemmas.main ⟨e, he⟩ g hg

end
end CrisExtensionUnit
namespace DeRhamHomExtUnit
section
universe u

theorem Bridge.CrisLoc.bdR_hom_ext_u : ∀ (l : ℕ) [Fact l.Prime] {R : Type u} [CommRing R] {f g : (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l)) →+* R} (h : ∀ x : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)), f (algebraMap _ _ x) = g (algebraMap _ _ x)), f = g := by
  intro l _ R _ f g h
  exact IsLocalization.ringHom_ext
    (nonZeroDivisors (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (RingHom.ext h)

end
end DeRhamHomExtUnit
