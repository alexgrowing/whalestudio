import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BSP.AinfDiv
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem cc_l : WittVector.constantCoeff (p := l) (R := OCb l) ((l : ℕ) : Ainf l) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

theorem dvd_iff (y : Ainf l) :
    ((l : ℕ) : Ainf l) ∣ y ↔ WittVector.constantCoeff (p := l) (R := OCb l) y = 0 := by
  rw [← RingHom.mem_ker, WittVector.ker_constantCoeff, Ideal.mem_span_singleton]

theorem dvd_E : ((l : ℕ) : Ainf l) ∣ bk.ev bk.E - bk.ev X ^ bk.Ep.natDegree := by
  have h := bk.monic.as_sum
  have : bk.E = X ^ bk.Ep.natDegree + ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * X ^ i := by
    change ((bk.Ep : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) = _
    conv_lhs => rw [h]
    rw [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X]
    congr 1
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp
  rw [this, map_add, map_pow, add_sub_cancel_left, map_sum]
  refine Finset.dvd_sum fun i hi => ?_
  obtain ⟨d, hd⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
  rw [hd, map_mul, map_mul, map_mul, map_natCast, map_natCast, mul_assoc]
  exact dvd_mul_right _ _

theorem cc_E : WittVector.constantCoeff (p := l) (R := OCb l) (bk.ev bk.E) = bk.flat ^ bk.Ep.natDegree := by
  have h := (dvd_iff _).1 (dvd_E bk)
  rw [map_sub, sub_eq_zero, map_pow, bk.ev_X] at h
  simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h ⊢
  exact h

theorem cc_E_ne : WittVector.constantCoeff (p := l) (R := OCb l) (bk.ev bk.E) ≠ 0 := by
  intro h
  have hu := (isUnit_inclW_of_span bk.span_ev).map (WittVector.constantCoeff (p := l) (R := Cb l))
  rw [WittVector.constantCoeff_apply, inclW, WittVector.map_coeff, ← WittVector.constantCoeff_apply, h,
    map_zero] at hu
  exact not_isUnit_zero hu

theorem flat_ne : bk.flat ≠ 0 := by
  intro h
  apply cc_E_ne bk
  rw [cc_E, h, zero_pow bk.deg_pos.ne']

theorem flat_not_unit : ¬ IsUnit bk.flat := by
  intro h
  have h1 : IsUnit (bk.ev bk.E) := by
    refine GlobalTheory.Per.AinfComplete.witt_isUnit _ ?_
    rw [cc_E]; exact h.pow _
  have h2 : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  have := h1.map (Per.θ l)
  rw [h2] at this
  exact not_isUnit_zero this

theorem flat_nil : IsNilpotent (Perfection.coeff (ModP (OC l) l) l 0 bk.flat) :=
  GlobalTheory.Per.AinfComplete.nilpotent_of_not_isUnit l _ fun h =>
    flat_not_unit bk (GlobalTheory.Per.AinfComplete.perfection_isUnit _ h)

theorem flat_haus (x : OCb l) (hx : ∀ n, bk.flat ^ n ∣ x) : x = 0 :=
  GlobalTheory.Per.AinfComplete.perfection_haus (flat_nil bk) x hx

theorem complete : IsAdicComplete (Ideal.span {bk.flat}) (OCb l) where
  haus' x hx := by
    refine flat_haus bk x fun n => ?_
    have := hx n
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.zero] at this
    exact Ideal.mem_span_singleton.1 this
  prec' := (GlobalTheory.Per.AinfComplete.precomplete_of_summ
    (GlobalTheory.Per.AinfComplete.summ_of_tails (GlobalTheory.Per.AinfComplete.perfection_tails (flat_nil bk)))).prec'

theorem dvd_of_dvd_X_mul (y : Ainf l) (h : ((l : ℕ) : Ainf l) ∣ bk.ev X * y) : ((l : ℕ) : Ainf l) ∣ y := by
  rw [dvd_iff] at h ⊢
  rw [map_mul, bk.ev_X, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h
  exact (mul_eq_zero.1 h).resolve_left (flat_ne bk)

theorem dvd_of_forall (y : Ainf l) (h : ∀ m : ℕ, ∃ z, ((l : ℕ) : Ainf l) ∣ y - bk.ev X ^ m * z) :
    ((l : ℕ) : Ainf l) ∣ y := by
  rw [dvd_iff]
  refine flat_haus bk _ fun m => ?_
  obtain ⟨z, hz⟩ := h m
  rw [dvd_iff, map_sub, sub_eq_zero, map_mul, map_pow, bk.ev_X] at hz
  simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at hz ⊢
  rw [hz]
  exact dvd_mul_right _ _

include bk in

theorem mem_pow (n : ℕ) (y : Ainf l)
    (h : ((l : ℕ) : Ainf l) * y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ (2 * n + 2)) :
    y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ n := by
  rw [← bk.span_ev] at h ⊢
  have h1 : (Ideal.span {((l : ℕ) : Ainf l)} ⊔ Ideal.span {bk.ev bk.E}) ^ (2 * n + 2) ≤
      Ideal.span {((l : ℕ) : Ainf l)} ^ (n + 1) ⊔ Ideal.span {bk.ev bk.E} ^ (n + 1) := by
    rw [show 2 * n + 2 = (n + 1) + (n + 1) by ring]
    exact Ideal.sup_pow_add_le_pow_sup_pow
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (h1 h)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hu hv
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  have hb : ((l : ℕ) : Ainf l) ∣ b := by
    rw [dvd_iff]
    have := congrArg (WittVector.constantCoeff (p := l) (R := OCb l)) huv
    simp only [map_add, map_mul, map_pow, cc_l, zero_pow (Nat.succ_ne_zero n), mul_zero, zero_mul,
      zero_add] at this
    exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ (cc_E_ne bk))
  obtain ⟨b', rfl⟩ := hb
  have hy : y = a * ((l : ℕ) : Ainf l) ^ n + b' * bk.ev bk.E ^ (n + 1) := by
    rw [← sub_eq_zero]
    apply ainf_torsionFree
    linear_combination -huv
  rw [hy]
  refine Ideal.add_mem _ ?_ ?_
  · refine Ideal.pow_right_mono le_sup_left n ?_
    rw [Ideal.span_singleton_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · refine Ideal.pow_right_mono le_sup_right n ?_
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.2 ⟨b' * bk.ev bk.E, by ring⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    (∀ (n : ℕ) (y : Ainf l), ((l : ℕ) : Ainf l) * y ∈
        (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ (2 * n + 2) →
      y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ n) ∧
    (∀ y : Ainf l, ((l : ℕ) : Ainf l) ∣ bk.ev X * y → ((l : ℕ) : Ainf l) ∣ y) ∧
    (∀ y : Ainf l, (∀ m : ℕ, ∃ z, ((l : ℕ) : Ainf l) ∣ y - bk.ev X ^ m * z) → ((l : ℕ) : Ainf l) ∣ y) ∧
    bk.flat ≠ 0 ∧ ¬ IsUnit bk.flat ∧ IsAdicComplete (Ideal.span {bk.flat}) (OCb l) ∧
    ((l : ℕ) : Ainf l) ∣ bk.ev bk.E - bk.ev X ^ bk.Ep.natDegree :=
  fun _ _ _ bk => ⟨mem_pow bk, dvd_of_dvd_X_mul bk, dvd_of_forall bk, flat_ne bk, flat_not_unit bk,
    complete bk, dvd_E bk⟩

end GlobalTheory.BSP.AinfDiv
