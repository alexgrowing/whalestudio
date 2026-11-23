import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LubinTateSeriesEqOfCoeffOneEq
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

namespace GlobalTheory.LTOmega

section General

open GlobalTheory.Per.AinfComplete

variable {A : Type} [CommRing A] {P : A} {l f : ℕ} [Fact l.Prime]

theorem step (hP : P ∣ (l : A)) (hf : 0 < f) {a b : A} {n : ℕ} (h : P ^ (n + 1) ∣ a - b) :
    P ^ (n + 2) ∣ (P * a + a ^ l ^ f) - (P * b + b ^ l ^ f) := by
  obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
  have h1 : a ^ l - b ^ l ∈ Ideal.span {P} ^ (n + 1 + 1) :=
    GlobalTheory.LTTilt.pow_l_sub_mem (j := n + 1) (Ideal.span {P}) (Ideal.mem_span_singleton.2 hP) (by omega)
      (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton.2 h)
  have h2 := GlobalTheory.LTTilt.pow_sub_mem _ h1 (l ^ k)
  rw [← pow_mul, ← pow_mul, ← pow_succ', Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
  have h3 : P ^ (n + 2) ∣ P * (a - b) := by
    rw [pow_succ' P (n + 1)]
    exact mul_dvd_mul_left P h
  convert dvd_add h3 h2 using 1
  ring

omit [Fact l.Prime] in
theorem dvd_of_map (F : A ≃+* A) (hF : F P = P) {n : ℕ} {a : A} (h : P ^ n ∣ F a) : P ^ n ∣ a := by
  have h1 : F.symm P = P := by rw [RingEquiv.symm_apply_eq, hF]
  have := map_dvd F.symm h
  rwa [map_pow, h1, F.symm_apply_apply] at this

theorem unique_lift [IsHausdorff (Ideal.span {P}) A] (hP : P ∣ (l : A)) (hf : 0 < f) (F : A ≃+* A) (hF : F P = P)
    {a b : A} (hab : P ∣ a - b) (ha : F a = P * a + a ^ l ^ f) (hb : F b = P * b + b ^ l ^ f) : a = b := by
  have key : ∀ n, P ^ (n + 1) ∣ a - b := fun n => by
    induction n with
    | zero => simpa using hab
    | succ n ih =>
      refine dvd_of_map F hF ?_
      rw [map_sub, ha, hb]
      exact step hP hf ih
  exact sub_eq_zero.1 (eq_zero_of_haus P _ fun n =>
    Ideal.mem_span_singleton.2 ((pow_dvd_pow P n.le_succ).trans (key n)))

theorem exists_lift [IsAdicComplete (Ideal.span {P}) A] (hP : P ∣ (l : A)) (hf : 0 < f) (F : A ≃+* A) (hF : F P = P)
    (hq : ∀ x, P ∣ F x - x ^ l ^ f) (x : A) : ∃ ω, P ∣ ω - x ∧ F ω = P * ω + ω ^ l ^ f := by
  let y : ℕ → A := fun n => (fun t => F.symm (P * t + t ^ l ^ f))^[n] x
  have hy : ∀ n, F (y (n + 1)) = P * y n + y n ^ l ^ f := fun n => by
    simp only [y, Function.iterate_succ_apply', RingEquiv.apply_symm_apply]
  have hd : ∀ n, P ^ (n + 1) ∣ y (n + 1) - y n := fun n => by
    induction n with
    | zero =>
      refine dvd_of_map F hF ?_
      rw [map_sub, hy, zero_add, pow_one]
      convert dvd_sub (dvd_mul_right P (y 0)) (hq (y 0)) using 1
      ring
    | succ n ih =>
      refine dvd_of_map F hF ?_
      rw [map_sub, hy, hy]
      exact step hP hf ih
  choose b hb using hd
  obtain ⟨L, hL⟩ := summ_of_precomplete P b
  have hs : ∀ n, y n = x + P * ∑ i ∈ Finset.range n, P ^ i * b i := fun n => by
    induction n with
    | zero => simp [y]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      linear_combination ih + hb n
  have hω : ∀ n, P ^ (n + 1) ∣ x + P * L - y n := fun n => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hL n)
    exact ⟨c, by rw [hs n]; linear_combination P * hc⟩
  refine ⟨x + P * L, ⟨L, by ring⟩, sub_eq_zero.1 (eq_zero_of_haus P _ fun n =>
    Ideal.mem_span_singleton.2 ((pow_dvd_pow P (by omega : n ≤ n + 2)).trans ?_))⟩
  have h1 := map_dvd F (hω (n + 1))
  rw [map_pow, hF, map_sub, hy] at h1
  convert dvd_sub h1 (step hP hf (hω n)) using 1
  ring

end General

section Series

open PowerSeries

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem dvd_aeval_sub {p r : Polynomial R} {n : ℕ} (h : (X : R⟦X⟧) ^ n ∣ (p : R⟦X⟧) - (r : R⟦X⟧)) (w : A) :
    w ^ n ∣ Polynomial.aeval w p - Polynomial.aeval w r := by
  have h1 : (Polynomial.X : Polynomial R) ^ n ∣ p - r := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    have := X_pow_dvd_iff.1 h d hd
    rwa [← Polynomial.coe_sub, Polynomial.coeff_coe] at this
  have := map_dvd (Polynomial.aeval w) h1
  rwa [map_pow, Polynomial.aeval_X, map_sub] at this

theorem aeval_trunc (φ : R⟦X⟧) (n : ℕ) (w : A) :
    Polynomial.aeval w (trunc n φ) = ∑ j ∈ Finset.range n, algebraMap R A (coeff j φ) * w ^ j := by
  rw [trunc_apply, map_sum, Finset.range_eq_Ico]
  exact Finset.sum_congr rfl fun j _ => Polynomial.aeval_monomial w

theorem trunc_comm {π : R} {q : ℕ} (hq : q ≠ 0) {φ : R⟦X⟧}
    (h : C π * φ + φ ^ q = subst (C π * X + X ^ q : R⟦X⟧) φ) (n : ℕ) (w : A) :
    w ^ n ∣ (algebraMap R A π * Polynomial.aeval w (trunc n φ) + Polynomial.aeval w (trunc n φ) ^ q) -
      Polynomial.aeval (algebraMap R A π * w + w ^ q) (trunc n φ) := by
  set p := trunc n φ with hp
  set e : R⟦X⟧ := C π * X + X ^ q with he
  have hs : HasSubst e := HasSubst.of_constantCoeff_zero' (by simp [he, hq])
  have hd : (X : R⟦X⟧) ^ n ∣ φ - (p : R⟦X⟧) := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, hp, coeff_trunc, if_pos hm, sub_self]
  let E : Polynomial R := Polynomial.C π * Polynomial.X + Polynomial.X ^ q
  have hE : (E : R⟦X⟧) = e := by simp [E, he]
  have h1 : ((p.comp E : Polynomial R) : R⟦X⟧) = subst e (p : R⟦X⟧) := by
    rw [subst_coe hs, Polynomial.comp_eq_aeval, ← hE]
    exact (Polynomial.aeval_algHom_apply (Polynomial.coeToPowerSeries.algHom R) E p).symm
  have h2 : (X : R⟦X⟧) ^ n ∣ subst e φ - subst e (p : R⟦X⟧) := by
    have := map_dvd (substAlgHom (S := R) hs) hd
    rw [map_pow, map_sub, substAlgHom_X, coe_substAlgHom] at this
    refine (pow_dvd_pow_of_dvd ?_ n).trans this
    exact dvd_add (dvd_mul_left _ _) (dvd_pow_self _ hq)
  have h3 : (X : R⟦X⟧) ^ n ∣ φ ^ q - (p : R⟦X⟧) ^ q := hd.trans (sub_dvd_pow_sub_pow _ _ _)
  have h4 := dvd_aeval_sub (p := Polynomial.C π * p + p ^ q) (r := p.comp E) (n := n) (by
    rw [h1, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C]
    convert dvd_sub (dvd_sub h2 h3) (Dvd.dvd.mul_left hd (C π)) using 1
    linear_combination h) w
  simpa [Polynomial.aeval_comp, E] using h4

end Series

section Core

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Prism GlobalTheory.AinfK GlobalTheory.LTTilt GlobalTheory.PZ GlobalTheory.Per.AinfComplete
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {π : ↥(OL K)}

theorem eq_zero_of_pow_dvd {p x : OC l} (hp : ¬ IsUnit p) (h : ∀ n, p ^ n ∣ x) : x = 0 := by
  have hk : ∀ n, ‖(x : ℂ_[l])‖ ≤ ‖(p : ℂ_[l])‖ ^ n := fun n => by
    have := (mem_span_iff_norm _ _).1 (Ideal.mem_span_singleton.2 (h n))
    rwa [SubmonoidClass.coe_pow, norm_pow] at this
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_lt_one_of_not_isUnit p hp)
  exact Subtype.ext (norm_le_zero_iff.1 (ge_of_tendsto' hlim hk))

theorem fK_pos : 0 < fK K := Nat.pos_of_ne_zero (NeZero.ne (fK K))

def frobE (K : FinExt l) : AK K ≃+* AK K := RingEquiv.ofBijective (frobq K).toRingHom (frobq_bijective K)

theorem frobE_apply (x : AK K) : frobE K x = frobq K x := rfl

theorem exists_not_mem (hπ : Irreducible π) {v : ℕ → OC l} (h1 : v 1 ≠ 0)
    (hv : ∀ n, intToOC K π * v (n + 1) + v (n + 1) ^ l ^ fK K = v n) : ∃ n, v n ∉ Ideal.span {intToOC K π} := by
  by_contra hcon
  push Not at hcon
  simp only [Ideal.mem_span_singleton] at hcon
  obtain ⟨m, hm⟩ : ∃ m, l ^ fK K = m + 2 := ⟨l ^ fK K - 2, by
    have := GlobalTheory.PZ.LTModel.two_le_resCard K
    change 2 ≤ l ^ fK K at this
    omega⟩
  have key : ∀ k n, intToOC K π ^ k ∣ v n := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      intro n
      have e : v n = v (n + 1) * (intToOC K π + v (n + 1) * v (n + 1) ^ m) := by
        rw [← hv n, hm]; ring
      rw [e, pow_succ]
      exact mul_dvd_mul (ih _) (dvd_add dvd_rfl ((hcon _).mul_right _))
  exact h1 (eq_zero_of_pow_dvd (not_isUnit_intToOC K hπ) fun k => key k 1)

theorem thetaK_eq (hπ : Irreducible π) {v : ℕ → OC l}
    (hv : ∀ n, intToOC K π * v (n + 1) + v (n + 1) ^ l ^ fK K = v n) {ω : AK K}
    (hx : IsTiltOf (fK K) (intToOC K π) (red K ω) v) (hω : frobq K ω = inO K π * ω + ω ^ l ^ fK K) :
    thetaK K ω = v 0 := by
  let w : ℕ → AK K := fun n => (frobE K).symm^[n] ω
  have hw : ∀ n, frobq K (w (n + 1)) = w n := fun n => by
    simp only [w, Function.iterate_succ_apply']
    exact (frobE K).apply_symm_apply _
  have hwe : ∀ n, frobq K (w n) = inO K π * w n + w n ^ l ^ fK K := fun n => by
    induction n with
    | zero => exact hω
    | succ n ih =>
      apply (frobq_bijective K).1
      rw [map_add, map_mul, map_pow, frobq_inO, hw, ih]
  have hr : ∀ n, red K ω = red K (w n) ^ l ^ (fK K * n) := fun n => by
    induction n with
    | zero => simp [w]
    | succ n ih => rw [ih, ← hw n, red_frobq, ← pow_mul, ← pow_add, Nat.mul_succ, add_comm (fK K)]
  have hl := natCast_mem_span_intToOC K hπ
  have h0 : ∀ n, intToOC K π ∣ thetaK K (w n) - v n := fun n => by
    obtain ⟨y, hy, hyv⟩ := hx n
    have h1 := coeff_eq_pow (red K (w n)) 0 (fK K * n)
    rw [zero_add, ← map_pow, ← hr, hy, ← PreTilt.mk_untilt_eq_coeff_zero, Ideal.Quotient.eq] at h1
    have h2 := Ideal.mem_span_singleton.1 (Ideal.span_le.2 (Set.singleton_subset_iff.2 hl) h1)
    convert dvd_add (dvd_add (dvd_thetaK_sub hπ (w n)) h2) (Ideal.mem_span_singleton.1 hyv) using 1
    ring
  have key : ∀ k n, intToOC K π ^ (k + 1) ∣ thetaK K (w n) - v n := fun k => by
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      intro n
      rw [← hw n, hwe, map_add, map_mul, map_pow, thetaK_inO, ← hv n]
      exact step (Ideal.mem_span_singleton.1 hl) fK_pos (ih (n + 1))
  exact sub_eq_zero.1 (eq_zero_of_pow_dvd (not_isUnit_intToOC K hπ) fun k =>
    (pow_dvd_pow _ k.le_succ).trans (key k 0))

theorem core (hπ : Irreducible π) {v : ℕ → OC l} (h0 : v 0 = 0) (h1 : v 1 ≠ 0)
    (hv : ∀ n, intToOC K π * v (n + 1) + v (n + 1) ^ l ^ fK K = v n) :
    ∃ ω : AK K, ω ≠ 0 ∧ thetaK K ω = 0 ∧ frobq K ω = inO K π * ω + ω ^ l ^ fK K ∧
      ∀ (g : ↥(GK K)) (φ : PowerSeries ↥(OL K)),
        PowerSeries.C π * φ + φ ^ l ^ fK K =
          PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ l ^ fK K : PowerSeries ↥(OL K)) φ →
        (∀ n, HasSum (fun i => ((intToOC K (PowerSeries.coeff i φ) * v n ^ i : OC l) : ℂ_[l]))
          ((Per.σO (g : GQ l) (v n) : OC l) : ℂ_[l])) →
        ∀ n, ω ^ n ∣ gal K g ω - ∑ j ∈ Finset.range n, inO K (PowerSeries.coeff j φ) * ω ^ j := by
  have hl := natCast_mem_span_intToOC K hπ
  have hu := not_isUnit_intToOC K hπ
  obtain ⟨x, hx, -⟩ := existsUnique_isTiltOf (fK K) fK_pos (intToOC K π) hu hl v fun n =>
    Ideal.mem_span_singleton.2 ⟨-v (n + 1), by rw [← hv n]; ring⟩
  obtain ⟨m, hm⟩ := exists_not_mem hπ h1 hv
  have hx0 : x ≠ 0 := ne_zero_of_isTiltOf hl hx m hm
  have hxu : ¬ IsUnit x := not_isUnit_of_isTiltOf hl hu hx (by rw [h0]; exact zero_mem _)
  have := complete_pi hπ
  obtain ⟨x', rfl⟩ := red_surjective K x
  obtain ⟨ω, hωx, hω⟩ := exists_lift (dvd_l hπ) fK_pos (frobE K) (frobq_inO K π) (dvd_frobq_sub hπ) x'
  rw [← (red_eq_iff hπ _ _).2 hωx] at hx hx0 hxu
  rw [frobE_apply] at hω
  refine ⟨ω, fun h => hx0 (by rw [h, map_zero]), (thetaK_eq hπ hv hx hω).trans h0, hω, fun g φ hφ hg => ?_⟩
  have hc := complete_single hxu
  obtain ⟨y, hy⟩ := summ_of_precomplete ω fun j => inO K (PowerSeries.coeff j φ)
  simp only [Ideal.mem_span_singleton, mul_comm (ω ^ _)] at hy
  suffices gal K g ω = y by rwa [this]
  refine unique_lift (dvd_l hπ) (fK_pos (K := K)) (frobE K) (frobq_inO K π) ((red_eq_iff hπ _ _).1 ?_) ?_ ?_
  · have hn : IsNilpotent (Perfection.coeff (ModP (OC l) l) l 0 (red K ω)) :=
      nilpotent_of_not_isUnit l _ fun h => hxu (perfection_isUnit (p := l) _ h)
    refine sub_eq_zero.1 (perfection_haus (p := l) (R := ModP (OC l) l) hn (red K (gal K g ω) - red K y) fun n => ?_)
    have e1 := Ideal.mem_span_singleton.1 (isTiltOf_eval K hπ hx hx0 φ hg (isTiltOf_σF hx (g : GQ l)) n)
    have e2 := map_dvd (red K) (hy n)
    simp only [map_pow, map_sub, map_sum, map_mul] at e2
    have e3 := dvd_sub e1 e2
    rwa [sub_sub_sub_cancel_right, ← red_gal] at e3
  · rw [frobE_apply, ← gal_frobq, hω]
    simp only [map_add, map_mul, map_pow, gal_inO]
  · rw [frobE_apply]
    refine sub_eq_zero.1 (eq_zero_of_haus ω _ fun n => Ideal.mem_span_singleton.2 ?_)
    have hq : l ^ fK K ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    have e0 := hy n
    rw [← aeval_trunc] at e0
    have e1 := map_dvd (frobq K) e0
    simp only [map_pow, map_sub] at e1
    rw [← Polynomial.aeval_algHom_apply (frobq K) ω] at e1
    simp only [hω] at e1
    have e2 := (pow_dvd_pow_of_dvd (dvd_add (dvd_mul_left ω (inO K π)) (dvd_pow_self ω hq)) n).trans e1
    have e3 := trunc_comm hq hφ n ω
    have e4 := e0.trans (sub_dvd_pow_sub_pow _ _ (l ^ fK K))
    convert dvd_sub (dvd_sub (dvd_sub e2 e3) e4) (e0.mul_left (inO K π)) using 1
    ring

end Core

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GlobalTheory.Prism GlobalTheory.LTTilt in

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z →
    ∃ ω : AK K, ω ≠ 0 ∧ thetaK K ω = 0 ∧ frobq K ω = inO K π * ω + ω ^ resCard K ∧
      ∀ (g : ↥(GK K)) (a : ↥(OL K)) (φ : PowerSeries ↥(OL K)), (a : ↥K.1) = (χ g : ↥K.1) → IsLTEndo K π a φ →
        ∀ n : ℕ, gal K g ω - ∑ j ∈ Finset.range n, inO K (PowerSeries.coeff j φ) * ω ^ j ∈
          RingHom.ker (thetaK K) ^ n := by
  intro l _ K χ π z ⟨hπ, hz0, hz1, hz, hg⟩
  have hq := GlobalTheory.PZ.LTModel.two_le_resCard K
  have hb : ∀ n, ‖z n‖ ≤ 1 := fun n => by
    induction n with
    | zero => simp [hz0]
    | succ n ih =>
      by_contra h
      rw [not_le] at h
      have e : z (n + 1) ^ resCard K = z n + -(((π : ↥K.1) : Om l) * z (n + 1)) := by rw [← hz n]; ring
      have h1 := IsUltrametricDist.norm_add_le_max (z n) (-(((π : ↥K.1) : Om l) * z (n + 1)))
      rw [← e, norm_pow, norm_neg, norm_mul] at h1
      have h2 : ‖z (n + 1)‖ < ‖z (n + 1)‖ ^ resCard K := lt_self_pow₀ h (by omega)
      have h3 := mul_le_of_le_one_left (norm_nonneg (z (n + 1))) (norm_le_one_of_mem_OL K π)
      exact absurd (h1.trans (max_le (ih.trans h.le) h3)) h2.not_ge
  let v : ℕ → OC l := fun n => ⟨algebraMap (Om l) ℂ_[l] (z n),
    (GlobalTheory.RingBasics.mem_OC _).2 ((PadicComplex.norm_extends l _).trans_le (hb n))⟩
  have hcoe : ∀ c : ↥(OL K), ((intToOC K c : OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] ((c : ↥K.1) : Om l) :=
    fun _ => rfl
  have hvc : ∀ n, (v n : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (z n) := fun _ => rfl
  obtain ⟨ω, hω0, hθ, hF, hG⟩ := core (K := K) hπ (v := v) (Subtype.ext (by rw [hvc, hz0, map_zero]; rfl))
    (fun h => hz1 ((algebraMap (Om l) ℂ_[l]).injective (by rw [← hvc, h, map_zero]; rfl))) fun n =>
      Subtype.ext (by
        push_cast
        rw [hcoe, hvc, hvc, ← hz n, map_add, map_mul, map_pow]
        rfl)
  refine ⟨ω, hω0, hθ, hF, fun g a φ ha hφ n => ?_⟩
  obtain ⟨a', ha', φ', hφ', hs⟩ := hg g
  obtain rfl : a = a' := Subtype.ext (ha.trans ha'.symm)
  obtain rfl := GlobalTheory.PZ.LTModel.IsLTEndo_unique hπ hφ hφ'
  obtain ⟨c, hc⟩ := hG g φ hφ.2.2 (fun m => by
    have h := (hs m).map (algebraMap (Om l) ℂ_[l]) (UniformSpace.Completion.continuous_coe _)
    have e : ((Per.σO (g : GQ l) (v m) : OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] ((g : GQ l) (z m)) :=
      (GlobalTheory.RingIface.sigO_coe l (g : GQ l) (v m)).trans (GlobalTheory.RingBasics.σC_coe (g : GQ l) (z m))
    rw [e]
    convert h using 2 with i
    push_cast
    rw [hcoe, hvc, Function.comp_apply, map_mul, map_pow]) n
  rw [hc]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hθ n)

end GlobalTheory.LTOmega
