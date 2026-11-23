import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionZeroOnePropertiesStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.WDiv

section General

variable (l : ℕ) {R : Type} [CommRing R] (ρ : ℝ≥0) (E : R⟦X⟧) (e : ℕ)

def Div (t : ℝ) (y : PreDisc l (X : R⟦X⟧) ρ) : Prop :=
  ∃ q ∈ ball l (X : R⟦X⟧) ρ t, ∃ c : Fin e → PreDisc l (0 : R) 1, (∀ i, c i ∈ ball l (0 : R) 1 t) ∧
    y = algebraMap R⟦X⟧ _ E * q +
      ∑ i, preMap l (0 : R) 1 (X : R⟦X⟧) ρ C (c i) * algebraMap R⟦X⟧ _ (X ^ (i : ℕ))

variable {l ρ E e}

theorem Div.mono {s t : ℝ} {y} (h : Div l ρ E e s y) (hst : s ≤ t) : Div l ρ E e t y := by
  obtain ⟨q, hq, c, hc, h⟩ := h
  exact ⟨q, ball_mono _ _ _ hst hq, c, fun i => ball_mono _ _ _ hst (hc i), h⟩

theorem Div.add {t : ℝ} {y y'} (h : Div l ρ E e t y) (h' : Div l ρ E e t y') : Div l ρ E e t (y + y') := by
  obtain ⟨q, hq, c, hc, rfl⟩ := h
  obtain ⟨q', hq', c', hc', rfl⟩ := h'
  refine ⟨q + q', add_mem hq hq', c + c', fun i => add_mem (hc i) (hc' i), ?_⟩
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  ring

theorem Div.zero {t : ℝ} : Div l ρ E e t 0 :=
  ⟨0, zero_mem _, 0, fun _ => zero_mem _, by simp⟩

theorem lpow_mem (hl : 0 < l) {A : Type} [CommRing A] (u : A) (σ : ℝ≥0) (a c : ℕ) :
    algebraMap A (PreDisc l u σ) ((l : A) ^ a) * IsLocalization.Away.invSelf (l : A) ^ c ∈
      ball l u σ ((l : ℝ) ^ c / (l : ℝ) ^ a) := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl
  exact Submodule.subset_span ⟨a, 0, c, by field_simp; simp, by simp⟩

theorem Div.lmul (hl : 0 < l) {t : ℝ} {y} (h : Div l ρ E e t y) (a c : ℕ) :
    Div l ρ E e ((l : ℝ) ^ c / (l : ℝ) ^ a * t)
      (algebraMap R⟦X⟧ _ ((l : R⟦X⟧) ^ a) * IsLocalization.Away.invSelf (l : R⟦X⟧) ^ c * y) := by
  obtain ⟨q, hq, d, hd, rfl⟩ := h
  refine ⟨_, mul_mem_ball _ _ _ (by positivity) (lpow_mem hl _ _ a c) hq, _,
    fun i => mul_mem_ball _ _ _ (by positivity) (lpow_mem hl _ _ a c) (hd i), ?_⟩
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, preMap_alg, map_pow (preMap l (0 : R) 1 (X : R⟦X⟧) ρ C), preMap_inv, map_pow C,
      map_natCast]
    ring

theorem alg_mem_ball {A : Type} [CommRing A] (u : A) (σ : ℝ≥0) (b : ℕ) (a : A) :
    algebraMap A (PreDisc l u σ) (u ^ b * a) ∈ ball l u σ ((σ : ℝ) ^ b) := by
  have h : algebraMap A (PreDisc l u σ) (u ^ b) ∈ ball l u σ ((σ : ℝ) ^ b) :=
    Submodule.subset_span ⟨0, b, 0, by simp, by simp⟩
  have := Submodule.smul_mem _ a h
  rwa [Algebra.smul_def, ← map_mul, mul_comm] at this

theorem div_monomial (hl : 0 < l) (he : 0 < e) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hρ : 1 ≤ (ρ : ℝ) ^ e * l)
    (z : R⟦X⟧) (hE : E = X ^ e + (l : R⟦X⟧) * z)
    (hdiv : ∀ a : R⟦X⟧, ∃ (q : R⟦X⟧) (c : Fin e → R), a = E * q + ∑ i, C (c i) * X ^ (i : ℕ)) (b : ℕ) :
    ∀ a : R⟦X⟧, Div l ρ E e ((ρ : ℝ) ^ b / (ρ : ℝ) ^ e) (algebraMap R⟦X⟧ _ (X ^ b * a)) := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl
  have h0 : (0 : ℝ) < ρ := hρ0
  have h1 : (ρ : ℝ) ≤ 1 := hρ1
  induction b using Nat.strong_induction_on with
  | _ b ih =>
  intro a
  rcases lt_or_ge b e with hb | hb
  · obtain ⟨q, c, h⟩ := hdiv (X ^ b * a)
    refine Div.mono (s := 1) ⟨algebraMap _ _ q, by simpa using alg_mem_ball (l := l) (X : R⟦X⟧) ρ 0 q,
      fun i => algebraMap _ _ (c i), fun i => by simpa using alg_mem_ball (l := l) (0 : R) 1 0 (c i), ?_⟩ ?_
    · rw [h]
      simp only [preMap_alg, map_add, map_mul, map_sum]
    · rw [one_le_div (by positivity)]
      exact pow_le_pow_of_le_one h0.le h1 hb.le
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' hb
    have e1 : algebraMap R⟦X⟧ (PreDisc l (X : R⟦X⟧) ρ) (X ^ (b + e) * a) =
        algebraMap R⟦X⟧ _ E * algebraMap R⟦X⟧ _ (X ^ b * a) +
        algebraMap R⟦X⟧ _ ((l : R⟦X⟧) ^ 1) * IsLocalization.Away.invSelf (l : R⟦X⟧) ^ 0 *
          algebraMap R⟦X⟧ _ (X ^ b * (-z * a)) := by
      rw [pow_zero, mul_one, ← map_mul, ← map_mul, ← map_add, hE]
      congr 1
      ring
    rw [e1]
    refine Div.add ⟨algebraMap _ _ (X ^ b * a), ?_, 0, fun _ => zero_mem _, by simp⟩ (((ih b (by omega) _).lmul hl 1 0).mono ?_)
    · rw [pow_add, mul_div_assoc, div_self (by positivity), mul_one]
      exact alg_mem_ball _ _ _ _
    · rw [pow_add, pow_zero, pow_one, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ (ρ : ℝ) ^ b * (ρ : ℝ) ^ e := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hρ this]

theorem div_ball (hl : 0 < l) (hρ0 : 0 < ρ)
    (hm : ∀ (b : ℕ) (a : R⟦X⟧), Div l ρ E e ((ρ : ℝ) ^ b / (ρ : ℝ) ^ e) (algebraMap R⟦X⟧ _ (X ^ b * a)))
    {r : ℝ} {y} (hy : y ∈ ball l (X : R⟦X⟧) ρ r) : ∀ a : R⟦X⟧, Div l ρ E e (r / (ρ : ℝ) ^ e) (a • y) := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl
  have h0 : (0 : ℝ) < ρ := hρ0
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, c, h1, rfl⟩ := hx
    intro s
    have := (hm b s).lmul hl a c
    refine Div.mono (by convert this using 1; simp only [Algebra.smul_def, map_mul]; ring) ?_
    rw [← mul_div_assoc, div_mul_eq_mul_div]
    gcongr
    rw [div_le_iff₀ (by positivity)]
    exact h1
  | zero => intro a; rw [smul_zero]; exact Div.zero
  | add x y _ _ hx hy => intro a; rw [smul_add]; exact (hx a).add (hy a)
  | smul a x _ hx => intro s; rw [smul_smul]; exact hx _

theorem norm_C_zero : ‖toDisc l (X : R⟦X⟧) ρ (C (0 : R))‖ ≤ ((1 : ℝ≥0) : ℝ) := norm_toDisc_le _

variable (l ρ R) in

def cMap [Fact l.Prime] : Disc l (0 : R) 1 →+* Disc l (X : R⟦X⟧) ρ :=
  Disc.map (u := (0 : R)) (ρ := 1) (C : R →+* R⟦X⟧) norm_C_zero

theorem isDiscMap_cMap [Fact l.Prime] : IsDiscMap (C : R →+* R⟦X⟧) (cMap l R ρ) := isDiscMap_map _ _

theorem div_disc [hl : Fact l.Prime] (hρ0 : 0 < ρ)
    (hm : ∀ (b : ℕ) (a : R⟦X⟧), Div l ρ E e ((ρ : ℝ) ^ b / (ρ : ℝ) ^ e) (algebraMap R⟦X⟧ _ (X ^ b * a)))
    (y : Disc l (X : R⟦X⟧) ρ) : ∃ (q : Disc l (X : R⟦X⟧) ρ) (c : Fin e → Disc l (0 : R) 1),
      y = toDisc l X ρ E * q + ∑ i, cMap l R ρ (c i) * toDisc l X ρ (X ^ (i : ℕ)) := by
  have h0 : (0 : ℝ) < ρ := hρ0
  set ι : Disc l (0 : R) 1 →+* Disc l (X : R⟦X⟧) ρ := cMap l R ρ with hι
  have hιm : IsDiscMap C ι := isDiscMap_cMap
  have hιp : ∀ x, ι (ofPre l (0 : R) 1 x) = ofPre l X ρ (preMap l (0 : R) 1 (X : R⟦X⟧) ρ C x) := by
    have e : ι.comp (ofPre l (0 : R) 1) = (ofPre l X ρ).comp (preMap l (0 : R) 1 (X : R⟦X⟧) ρ C) :=
      IsLocalization.ringHom_ext (Submonoid.powers (l : R)) (RingHom.ext fun a =>
        (hιm.ext a).trans (congrArg (ofPre l X ρ) (preMap_alg (l := l) (u := (0 : R)) (ρ := 1) (u' := (X : R⟦X⟧))
          (ρ' := ρ) (C : R →+* R⟦X⟧) a)).symm)
    exact fun x => RingHom.congr_fun e x
  let f0 : (Disc l (X : R⟦X⟧) ρ × (Fin e → Disc l (0 : R) 1)) →+ Disc l (X : R⟦X⟧) ρ :=
    { toFun := fun g => toDisc l X ρ E * g.1 + ∑ i, ι (g.2 i) * toDisc l X ρ (X ^ (i : ℕ))
      map_zero' := by simp
      map_add' := fun g g' => by
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
        ring }
  have hb : ∀ g, ‖f0 g‖ ≤ (1 + e) * ‖g‖ := fun g => by
    refine (norm_add_le _ _).trans ?_
    rw [add_mul]
    refine add_le_add ((norm_mul_le _ _).trans
      (mul_le_mul (norm_toDisc_le _) (norm_fst_le g) (norm_nonneg _) zero_le_one)) ((norm_sum_le _ _).trans ?_)
    refine (Finset.sum_le_card_nsmul _ _ ‖g‖ fun i _ => ?_).trans (by simp)
    refine (norm_mul_le _ _).trans ((mul_le_mul ((hιm.norm_le _).trans ((norm_le_pi_norm _ i).trans
      (norm_snd_le g))) (norm_toDisc_le _) (norm_nonneg _) (norm_nonneg _)).trans (mul_one _).le)
  let f := f0.mkNormedAddGroupHom _ hb
  have hs : f.SurjectiveOnWith (ofPre l (X : R⟦X⟧) ρ).toAddMonoidHom.range (2 / (ρ : ℝ) ^ e) := by
    rintro _ ⟨x, rfl⟩
    change ∃ g, f0 g = ofPre l X ρ x ∧ ‖g‖ ≤ _ * ‖ofPre l X ρ x‖
    rcases (norm_nonneg (ofPre l X ρ x)).eq_or_lt with h | h
    · exact ⟨0, by rw [map_zero, norm_eq_zero.1 h.symm], by rw [← h]; simp⟩
    · have hx : x ∈ ball l (X : R⟦X⟧) ρ (2 * ‖ofPre l X ρ x‖) :=
        mem_ball_of_gauge_lt _ _ _ (by rw [← norm_ofPre]; linarith)
      obtain ⟨q, hq, c, hc, h2⟩ := div_ball hl.out.pos hρ0 hm hx 1
      rw [one_smul] at h2
      have hp : 0 < 2 * ‖ofPre l X ρ x‖ / (ρ : ℝ) ^ e := by positivity
      refine ⟨(ofPre _ _ _ q, fun i => ofPre _ _ _ (c i)), ?_, ?_⟩
      · conv_rhs => rw [h2]
        simp only [f0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_add, map_mul, map_sum, hιp]
        rfl
      · rw [div_mul_eq_mul_div]
        refine max_le ?_ ((pi_norm_le_iff_of_nonneg hp.le).2 fun i => ?_)
        · exact (norm_ofPre _ _ _ _).trans_le (gauge_le _ _ _ hp hq)
        · exact (norm_ofPre _ _ _ _).trans_le (gauge_le _ _ _ hp (hc i))
  obtain ⟨g, hg, -⟩ := controlled_closure_of_complete (by positivity) one_pos hs y (denseRange_ofPre l X ρ y)
  exact ⟨g.1, g.2, hg.symm⟩

theorem coe_sum_fin (c : Fin e → R) :
    ((∑ i, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ) : Polynomial R) : R⟦X⟧) = ∑ i, C (c i) * X ^ (i : ℕ) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  simp [Polynomial.coeToPowerSeries.ringHom_apply]

theorem div_disc_poly [hl : Fact l.Prime] (hρ0 : 0 < ρ)
    (hm : ∀ (b : ℕ) (a : R⟦X⟧), Div l ρ E e ((ρ : ℝ) ^ b / (ρ : ℝ) ^ e) (algebraMap R⟦X⟧ _ (X ^ b * a)))
    (hk0 : ∀ x : Disc l (0 : R) 1, ‖x‖ ≤ 1 → ∃ w, x = toDisc l (0 : R) 1 w)
    (y : Disc l (X : R⟦X⟧) ρ) : ∃ (q : Disc l (X : R⟦X⟧) ρ) (k : ℕ) (r : Polynomial R), r.degree < e ∧
      ((l : ℕ) : Disc l (X : R⟦X⟧) ρ) ^ k * y = toDisc l X ρ E * q + toDisc l X ρ (r : R⟦X⟧) := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hl1 : (1 : ℝ) < l := Nat.one_lt_cast.2 hl.out.one_lt
  obtain ⟨q, c, h⟩ := div_disc hρ0 hm y
  have hln : ‖((l : ℕ) : Disc l (0 : R) 1)‖ ≤ (l : ℝ)⁻¹ := by
    have := gauge_le _ _ _ (by positivity) (lpow_mem hl.out.pos (0 : R) 1 1 0)
    rw [← norm_ofPre] at this
    simpa using this
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖c‖) hl1
  have hw : ∀ i, ∃ w, ((l : ℕ) : Disc l (0 : R) 1) ^ (k + 1) * c i = toDisc l (0 : R) 1 w := fun i => by
    refine hk0 _ ((norm_mul_le _ _).trans ?_)
    have h1 : ‖((l : ℕ) : Disc l (0 : R) 1) ^ (k + 1)‖ ≤ ((l : ℝ)⁻¹) ^ (k + 1) :=
      (norm_pow_le' _ k.succ_pos).trans (by gcongr)
    have h2 : ‖c i‖ ≤ (l : ℝ) ^ (k + 1) :=
      (norm_le_pi_norm c i).trans (hk.le.trans (pow_le_pow_right₀ hl1.le k.le_succ))
    refine (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)).trans ?_
    rw [← mul_pow, inv_mul_cancel₀ hl0.ne', one_pow]
  choose w hw using hw
  refine ⟨((l : ℕ) : Disc l (X : R⟦X⟧) ρ) ^ (k + 1) * q, k + 1,
    ∑ i, Polynomial.C (w i) * Polynomial.X ^ (i : ℕ), Polynomial.degree_sum_fin_lt w, ?_⟩
  rw [h, coe_sum_fin, map_sum, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← isDiscMap_cMap.ext, ← hw, map_mul (cMap l R ρ), map_pow (cMap l R ρ), map_natCast, mul_assoc]

theorem eq_X_pow_add {P : Polynomial R} (hP : P.Monic) (hd : ∀ i < P.natDegree, (l : R) ∣ P.coeff i) :
    ∃ z : R⟦X⟧, (P : R⟦X⟧) = X ^ P.natDegree + (l : R⟦X⟧) * z := by
  choose d hd using hd
  refine ⟨∑ i : Fin P.natDegree, C (d i i.2) * X ^ (i : ℕ), ?_⟩
  have h := congrArg (fun p : Polynomial R => (p : R⟦X⟧)) hP.as_sum
  simp only [Finset.sum_range, Polynomial.coe_add, coe_sum_fin, Polynomial.coe_pow, Polynomial.coe_X] at h
  refine h.trans ?_
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd i i.2, map_mul, map_natCast, mul_assoc]

theorem exists_div {P : Polynomial R} {I : Ideal R} [IsAdicComplete I R] (hdist : P.IsDistinguishedAt I)
    (hI : I ≠ ⊤) (a : R⟦X⟧) : ∃ (q : R⟦X⟧) (c : Fin P.natDegree → R),
      a = (P : R⟦X⟧) * q + ∑ i, C (c i) * X ^ (i : ℕ) := by
  obtain ⟨h1, h2⟩ := (hdist.isWeierstrassDivisorAt hI).isWeierstrassDivisionAt_div_mod a
  refine ⟨(hdist.isWeierstrassDivisorAt hI).div a, fun i => ((hdist.isWeierstrassDivisorAt hI).mod a).coeff i,
    h2.trans ?_⟩
  rw [← coe_sum_fin]
  congr 2
  have ho : P.natDegree = _ := congr(ENat.toNat $(hdist.coe_natDegree_eq_order_map (P : R⟦X⟧) 1
    (by rwa [constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)))
  rw [← ho] at h1
  rw [Polynomial.sum_fin (fun i a => Polynomial.C a * Polynomial.X ^ i) (by simp) h1,
    Polynomial.sum_C_mul_X_pow_eq]

end General

theorem weierstrass_div : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 →
    ∀ y : bk.DS ρ, ∃ (q : bk.DS ρ) (k : ℕ) (r : Polynomial (Wq l bk.a)), r.degree < bk.Ep.degree ∧
      ((l : ℕ) : bk.DS ρ) ^ k * y = toDisc l (X : bk.S) ρ bk.E * q + toDisc l (X : bk.S) ρ (r : bk.S) := by
  intro l hl K bk ρ hρ hρ1 y
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hl1 : (1 : ℝ) < l := Nat.one_lt_cast.2 hl.out.one_lt
  have he := bk.deg_pos
  have hρ0 : 0 < ρ := lt_of_lt_of_le (NNReal.rpow_pos (Nat.cast_pos.2 hl.out.pos)) hρ
  have hρe : 1 ≤ (ρ : ℝ) ^ bk.Ep.natDegree * l := by
    have h1 : (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree = (l : ℝ)⁻¹ := by
      have : (bk.Ep.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.2 he.ne'
      rw [BK.ρ₀, NNReal.coe_rpow, NNReal.coe_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le,
        neg_mul, one_div_mul_cancel this, Real.rpow_neg_one]
    have h2 : (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree ≤ (ρ : ℝ) ^ bk.Ep.natDegree := by gcongr
    rw [h1] at h2
    rwa [← inv_le_iff_one_le_mul₀ hl0]
  have hdist : bk.Ep.IsDistinguishedAt (Ideal.span {(l : Wq l bk.a)}) :=
    ⟨⟨fun hn => Ideal.mem_span_singleton.2 (bk.dvd_coeff _ hn)⟩, bk.monic⟩
  have hI : Ideal.span {(l : Wq l bk.a)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (WittVector.irreducible l).not_isUnit
  obtain ⟨z, hz⟩ := eq_X_pow_add bk.monic bk.dvd_coeff
  rw [Polynomial.degree_eq_natDegree bk.monic.ne_zero]
  exact div_disc_poly hρ0 (div_monomial hl.out.pos he hρ0 hρ1.le hρe z hz (exists_div hdist hI))
    (GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties l K bk).2.1 y

end GlobalTheory.BSP.WDiv
