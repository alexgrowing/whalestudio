import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.UnrWitt

variable {l : ℕ} [hl : Fact l.Prime]

theorem coeC (z : Om l) : (z : ℂ_[l]) = algebraMap (Om l) ℂ_[l] z := rfl

theorem norm_l_C : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l, norm_algebraMap', Padic.norm_p]

theorem norm_l_Om : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  rw [← PadicComplex.norm_extends l (l : Om l), coeC, map_natCast, norm_l_C]

theorem norm_OC_le (x : OC l) : ‖(x : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 x.2

theorem mem_OL_of_norm_le (K : FinExt l) (y : ↥K.1) (h : ‖(y : Om l)‖ ≤ 1) : y ∈ OL K := by
  have hi : IsIntegral ℚ_[l] (y : Om l) := Algebra.IsIntegral.isIntegral _
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hi)] at h
  have hl : minpoly ℚ_[l] (y : Om l) ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hi)
  have h1 : IsIntegral ℤ_[l] (y : Om l) := ⟨q, hm, by
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩
  exact (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).1 h1

theorem norm_pi_lt {K : FinExt l} (bk : BK K) : ‖((Per.θ l (bk.ev X) : OC l) : ℂ_[l])‖ < 1 := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  set φ : Wq l bk.a →+* ℂ_[l] := (PadicComplexInt l).toSubring.subtype.comp ((Per.θ l).comp (wA l bk.a).toRingHom) with hφ
  set π : ℂ_[l] := ((Per.θ l (bk.ev X) : OC l) : ℂ_[l]) with hπ
  have hπ1 : ‖π‖ ≤ 1 := norm_OC_le _
  have h0 : bk.Ep.eval₂ φ π = 0 := by
    have h1 : Per.θ l (bk.ev bk.E) = 0 := by
      have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
      exact this
    have h2 := congrArg (PadicComplexInt l).toSubring.subtype h1
    rw [BK.E, ← Polynomial.eval₂_C_X_eq_coe, Polynomial.hom_eval₂, Polynomial.hom_eval₂,
      Polynomial.hom_eval₂, map_zero] at h2
    have hc : (PadicComplexInt l).toSubring.subtype.comp ((Per.θ l).comp (bk.ev.comp C)) = φ :=
      RingHom.ext fun w => by simp [hφ, bk.ev_C]
    rw [hc] at h2
    exact h2
  have hcoef : ∀ i < bk.Ep.natDegree, ‖φ (bk.Ep.coeff i)‖ ≤ ‖(l : ℂ_[l])‖ := by
    intro i hi
    obtain ⟨c, hc⟩ := bk.dvd_coeff i hi
    rw [hc, map_mul, map_natCast, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_OC_le (Per.θ l (wA l bk.a c)))
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, bk.monic.coeff_natDegree, map_one, one_mul] at h0
  have h3 : π ^ bk.Ep.natDegree = -∑ i ∈ Finset.range bk.Ep.natDegree, φ (bk.Ep.coeff i) * π ^ i := by
    linear_combination h0
  have h4 : ‖π‖ ^ bk.Ep.natDegree ≤ ‖(l : ℂ_[l])‖ := by
    rw [← norm_pow, h3, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i hi => ?_
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hπ1)).trans
      (hcoef i (Finset.mem_range.1 hi))
  rw [norm_l_C] at h4
  by_contra h5
  push_neg at h5
  have h6 := one_le_pow₀ (n := bk.Ep.natDegree) h5
  have h7 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  linarith

end GlobalTheory.UnrWitt

namespace GlobalTheory.UnrWitt

variable {l : ℕ} [hl : Fact l.Prime]

theorem step {K : FinExt l} (bk : BK K) (y : Om l) (hyK : y ∈ K.1) (hyU : y ∈ MaximalUnramifiedExtension l) (hy1 : ‖y‖ ≤ 1) :
    ∃ (w : Wq l bk.a) (y' : Om l), y' ∈ K.1 ∧ y' ∈ MaximalUnramifiedExtension l ∧ ‖y'‖ ≤ 1 ∧
      (y : ℂ_[l]) = ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) + (l : ℂ_[l]) * (y' : ℂ_[l]) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  let r : ↥(OL K) := ⟨⟨y, hyK⟩, mem_OL_of_norm_le K _ hy1⟩
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (bk.str r)
  have hθ : (y : ℂ_[l]) = ((Per.θ l (bk.ev f) : OC l) : ℂ_[l]) := by
    rw [bk.θ_ev r f hf, coe_intToOC]
  set z : Fq l bk.a := (constantCoeff f).coeff 0 with hz
  obtain ⟨u, hu⟩ : (l : Wq l bk.a) ∣ constantCoeff f - WittVector.teichmuller l z := by
    rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub]
    simp [WittVector.constantCoeff_apply, hz]
  set f' : bk.S := PowerSeries.mk fun p => coeff (p + 1) f
  have hfe : f = X * f' + C (constantCoeff f) := eq_X_mul_shift_add_const f
  have hc : constantCoeff f = WittVector.teichmuller l z + (l : Wq l bk.a) * u := by rw [← hu]; ring
  set Ψ : bk.S →+* ℂ_[l] := (PadicComplexInt l).toSubring.subtype.comp ((Per.θ l).comp bk.ev) with hΨ
  have hΨC : ∀ w, Ψ (C w) = ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) := fun w => by simp [hΨ, bk.ev_C]
  set π : ℂ_[l] := ((Per.θ l (bk.ev X) : OC l) : ℂ_[l]) with hπ
  set t : ℂ_[l] := ((Per.θ l (wA l bk.a (WittVector.teichmuller l z)) : OC l) : ℂ_[l]) with ht
  set A : ℂ_[l] := ((Per.θ l (wA l bk.a u) : OC l) : ℂ_[l]) with hA
  set B : ℂ_[l] := ((Per.θ l (bk.ev f') : OC l) : ℂ_[l]) with hB
  have hdec : (y : ℂ_[l]) = t + (l : ℂ_[l]) * A + π * B := by
    have e1 : (y : ℂ_[l]) = Ψ f := hθ
    have e2 : Ψ X = π := rfl
    have e3 : Ψ f' = B := rfl
    rw [e1, hfe, hc]
    simp only [map_add, map_mul, map_natCast, hΨC, e2, e3]
    rw [ht, hA]
    ring

  set rt : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ (C (WittVector.teichmuller l z))) with hrt
  have htK : t = (((rt : ↥K.1) : Om l) : ℂ_[l]) := by
    rw [← coe_intToOC, ← bk.θ_ev rt (C (WittVector.teichmuller l z)) (by rw [hrt, RingEquiv.apply_symm_apply]), bk.ev_C]
  set yt : Om l := ((rt : ↥K.1) : Om l) with hyt
  have hytK : yt ∈ K.1 := (rt : ↥K.1).2
  have hteich : (WittVector.teichmuller l z) ^ (l ^ bk.a) = WittVector.teichmuller l z := by
    rw [← map_pow, Fq.pow_card]
  have hyt_pow : yt ^ (l ^ bk.a) = yt := by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_pow, ← coeC, ← htK, ht, ← SubmonoidClass.coe_pow, ← map_pow, ← map_pow, hteich]
  have hytU : yt ∈ MaximalUnramifiedExtension l := by
    by_cases h0 : yt = 0
    · rw [h0]; exact zero_mem _
    · have hq : 1 < l ^ bk.a := one_lt_pow_l l bk.a
      refine IntermediateField.subset_adjoin ℚ_[l] _ ⟨l ^ bk.a - 1, by omega, fun h => ?_, ?_⟩
      · exact hl.out.not_dvd_one ((Nat.dvd_sub_iff_right hq.le (dvd_pow_self l (NeZero.ne bk.a))).1 h)
      · apply mul_right_cancel₀ h0
        rw [← pow_succ, Nat.sub_add_cancel hq.le, hyt_pow, one_mul]

  have hdK : y - yt ∈ K.1 := sub_mem hyK hytK
  have hdU : y - yt ∈ MaximalUnramifiedExtension l := sub_mem hyU hytU
  have hdC : ((y - yt : Om l) : ℂ_[l]) = (l : ℂ_[l]) * A + π * B := by
    rw [coeC, map_sub, ← coeC, ← coeC, hdec, ← htK]
    ring
  have hd1 : ‖y - yt‖ < 1 := by
    rw [← PadicComplex.norm_extends, hdC]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul, norm_l_C]
      exact (mul_le_of_le_one_right (by positivity) (norm_OC_le _)).trans_lt (inv_lt_one_of_one_lt₀ hl1)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (norm_OC_le _)).trans_lt (norm_pi_lt bk)
  have hd2 : ‖y - yt‖ ≤ (l : ℝ)⁻¹ := by
    by_cases h0 : y - yt = 0
    · rw [h0, norm_zero]; positivity
    obtain ⟨k, hk⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow hdU h0
    rw [hk] at hd1 ⊢
    have hk0 : k < 0 := by
      by_contra hk0
      push_neg at hk0
      exact absurd hd1 (not_lt.2 (one_le_zpow₀ hl1.le hk0))
    calc (l : ℝ) ^ k ≤ (l : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hl1.le (by omega)
      _ = (l : ℝ)⁻¹ := zpow_neg_one _
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  refine ⟨WittVector.teichmuller l z, (y - yt) / (l : Om l), div_mem hdK (natCast_mem _ l),
    div_mem hdU (natCast_mem _ l), ?_, ?_⟩
  · rw [norm_div, norm_l_Om, div_inv_eq_mul]
    calc ‖y - yt‖ * l ≤ (l : ℝ)⁻¹ * l := by gcongr
      _ = 1 := inv_mul_cancel₀ (by positivity)
  · have hlC : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
    rw [coeC ((y - yt) / (l : Om l)), map_div₀, map_natCast, ← coeC, hdC, hdec]
    field_simp
    ring

end GlobalTheory.UnrWitt

namespace GlobalTheory.UnrWitt

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_of_int {K : FinExt l} (bk : BK K) (y : Om l) (hyK : y ∈ K.1) (hyU : y ∈ MaximalUnramifiedExtension l) (hy1 : ‖y‖ ≤ 1) :
    ∃ w : Wq l bk.a, ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) = (y : ℂ_[l]) := by
  classical
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  let N : Type := {y : Om l // y ∈ K.1 ∧ y ∈ MaximalUnramifiedExtension l ∧ ‖y‖ ≤ 1}
  let Φ : Wq l bk.a →+* ℂ_[l] := (PadicComplexInt l).toSubring.subtype.comp ((Per.θ l).comp (wA l bk.a).toRingHom)
  have hΦ : ∀ w, Φ w = ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) := fun _ => rfl
  have hΦ1 : ∀ w, ‖Φ w‖ ≤ 1 := fun w => norm_OC_le _
  have hs : ∀ v : N, ∃ p : Wq l bk.a × N,
      ((v.1 : Om l) : ℂ_[l]) = Φ p.1 + (l : ℂ_[l]) * ((p.2.1 : Om l) : ℂ_[l]) := by
    intro v
    obtain ⟨w, y', h1, h2, h3, h⟩ := step bk v.1 v.2.1 v.2.2.1 v.2.2.2
    exact ⟨(w, ⟨y', h1, h2, h3⟩), h⟩
  choose g hg using hs
  let ys : ℕ → N := fun k => Nat.rec (motive := fun _ => N) ⟨y, hyK, hyU, hy1⟩ (fun _ v => (g v).2) k
  have hys : ∀ k, ys (k + 1) = (g (ys k)).2 := fun _ => rfl
  let s : ℕ → Wq l bk.a := fun k => ∑ i ∈ Finset.range k, (l : Wq l bk.a) ^ i * (g (ys i)).1
  have hinv : ∀ k, (y : ℂ_[l]) = Φ (s k) + (l : ℂ_[l]) ^ k * (((ys k).1 : Om l) : ℂ_[l]) := by
    intro k
    induction k with
    | zero => simp [s, ys]
    | succ k ih =>
      have h := hg (ys k)
      rw [← hys] at h
      simp only [s, Finset.sum_range_succ, map_add, map_mul, map_pow, map_natCast]
      linear_combination ih + (l : ℂ_[l]) ^ k * h
  have hcau : ∀ m n, m ≤ n → (l : Wq l bk.a) ^ m ∣ s n - s m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have e : s (n + 1) - s m = (s n - s m) + (l : Wq l bk.a) ^ n * (g (ys n)).1 := by
        simp only [s, Finset.sum_range_succ]; ring
      rw [e]
      exact dvd_add ih (Dvd.dvd.mul_right (pow_dvd_pow _ hmn) _)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(l : Wq l bk.a)}) s fun {m n} hmn => by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (dvd_sub_comm).1 (hcau m n hmn)
  refine ⟨L, ?_⟩
  rw [← hΦ]
  have hbd : ∀ n : ℕ, ‖(y : ℂ_[l]) - Φ L‖ ≤ ((l : ℝ)⁻¹) ^ n := by
    intro n
    have h := hL n
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    obtain ⟨v, hv⟩ := h
    have e : (y : ℂ_[l]) - Φ L = (l : ℂ_[l]) ^ n * (Φ v + (((ys n).1 : Om l) : ℂ_[l])) := by
      have := congrArg Φ hv
      rw [map_sub, map_mul, map_pow, map_natCast] at this
      linear_combination hinv n + this
    rw [e, norm_mul, norm_pow, norm_l_C]
    refine mul_le_of_le_one_right (by positivity) ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hΦ1 v) ?_))
    rw [PadicComplex.norm_extends]
    exact (ys n).2.2.2
  by_contra hne
  have hpos : 0 < ‖(y : ℂ_[l]) - Φ L‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl1)
  exact absurd (hbd n) (not_le.2 hn)

theorem exists_pow_mul_eq_theta : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (x : Om l), x ∈ K.1 →
    x ∈ MaximalUnramifiedExtension l → ∃ (n : ℕ) (w : Wq l bk.a),
      ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) = ((((l : Om l) ^ n * x : Om l)) : ℂ_[l]) := by
  intro l _ K bk x hxK hxU
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖x‖ hl1
  have h1 : ‖(l : Om l) ^ n * x‖ ≤ 1 := by
    rw [norm_mul, norm_pow, norm_l_Om, inv_pow]
    rw [inv_mul_le_iff₀ (by positivity), mul_one]
    exact hn.le
  obtain ⟨w, hw⟩ := exists_of_int bk _ (mul_mem (pow_mem (natCast_mem _ l) n) hxK)
    (mul_mem (pow_mem (natCast_mem _ l) n) hxU) h1
  exact ⟨n, w, hw⟩

end GlobalTheory.UnrWitt
