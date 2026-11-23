import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSubOnePowTotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltNormUltrametricEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisMuBound

variable {l : ℕ} [hl : Fact l.Prime]

theorem sup_pow_le {R : Type*} [CommRing R] (A B : Ideal R) (k : ℕ) :
    (A ⊔ B) ^ (k + 1) ≤ A * (A ⊔ B) ^ k ⊔ B ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hX : A * (A ⊔ B) ^ k ⊔ B ^ (k + 1) ≤ (A ⊔ B) ^ (k + 1) :=
      sup_le (by rw [pow_succ']; exact Ideal.mul_mono_left le_sup_left)
        (Ideal.pow_right_mono le_sup_right _)
    calc (A ⊔ B) ^ (k + 1 + 1) = (A ⊔ B) * (A ⊔ B) ^ (k + 1) := pow_succ' _ _
      _ ≤ (A ⊔ B) * (A * (A ⊔ B) ^ k ⊔ B ^ (k + 1)) := Ideal.mul_mono_right ih
      _ = A * (A * (A ⊔ B) ^ k ⊔ B ^ (k + 1)) ⊔ (B * (A * (A ⊔ B) ^ k) ⊔ B * B ^ (k + 1)) := by
          rw [Ideal.sup_mul, Ideal.mul_sup B]
      _ ≤ A * (A ⊔ B) ^ (k + 1) ⊔ B ^ (k + 1 + 1) := by
          refine sup_le (le_sup_of_le_left (Ideal.mul_mono_right hX)) (sup_le ?_ ?_)
          · refine le_sup_of_le_left ?_
            rw [mul_left_comm]
            exact Ideal.mul_mono_right (by rw [pow_succ']; exact Ideal.mul_mono_left le_sup_right)
          · exact le_sup_of_le_right (by rw [← pow_succ'])

abbrev Tw (ϖ : OCb l) : Ainf l := WittVector.teichmuller l ϖ ^ (l - 1)

abbrev Iw (ϖ : OCb l) : Ideal (Ainf l) := Ideal.span {(l : Ainf l)} ⊔ Ideal.span {Tw ϖ}

theorem l_mem_Iw (ϖ : OCb l) : (l : Ainf l) ∈ Iw ϖ :=
  Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)

theorem T_mem_Iw (ϖ : OCb l) : Tw ϖ ∈ Iw ϖ :=
  Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

theorem cc_natCast_l : WittVector.constantCoeff (l : Ainf l) = 0 := by
  rw [map_natCast]; exact CharP.cast_eq_zero _ l

theorem cc_teich (x : OCb l) : WittVector.constantCoeff (WittVector.teichmuller l x) = x := by
  rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem l_dvd_sub_teich (c : Ainf l) :
    (l : Ainf l) ∣ c - WittVector.teichmuller l (WittVector.constantCoeff c) := by
  have h0 := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff c 0
  have hI : (Finset.Iic 0 : Finset ℕ) = {0} := by ext i; simp
  rw [hI, Finset.sum_singleton] at h0
  simpa [WittVector.constantCoeff_apply] using h0

theorem l_dvd_of_cc {c : Ainf l} (h : WittVector.constantCoeff c = 0) : (l : Ainf l) ∣ c := by
  simpa [h] using l_dvd_sub_teich c

theorem l_ne_zero_ainf : (l : Ainf l) ≠ 0 := by
  intro h
  have h1 := congrArg (Per.θ l) h
  rw [map_natCast, map_zero] at h1
  exact GlobalTheory.RingBasics.p_ne_zero (p := l) (by simpa using congrArg Subtype.val h1)

theorem mem_of_l_mul {ϖ : OCb l} (hϖ : ϖ ≠ 0) (k : ℕ) {y : Ainf l}
    (h : (l : Ainf l) * y ∈ Iw ϖ ^ (k + 1)) : y ∈ Iw ϖ ^ k := by
  have h1 := sup_pow_le _ _ k h
  rw [Ideal.span_singleton_pow, Submodule.mem_sup] at h1
  obtain ⟨u, hu, v, hv, huv⟩ := h1
  obtain ⟨u', hu', rfl⟩ := Ideal.mem_span_singleton_mul.1 hu
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hv
  have hc : WittVector.constantCoeff c = 0 := by
    have := congrArg WittVector.constantCoeff huv
    rw [map_add, map_mul, map_mul, map_mul, map_pow, map_pow, cc_natCast_l, cc_teich] at this
    simp only [zero_mul, zero_add] at this
    exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ (pow_ne_zero _ hϖ))
  obtain ⟨c', rfl⟩ := l_dvd_of_cc hc
  have h2 : (l : Ainf l) * (y - (u' + c' * Tw ϖ ^ (k + 1))) = 0 := by
    rw [mul_sub, ← huv]; ring
  rw [sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left l_ne_zero_ainf)]
  refine Ideal.add_mem _ hu' (Ideal.mul_mem_left _ _ ?_)
  exact Ideal.pow_le_pow_right (Nat.le_succ k) (Ideal.pow_mem_pow (T_mem_Iw ϖ) _)

theorem mem_of_l_pow_mul {ϖ : OCb l} (hϖ : ϖ ≠ 0) (m : ℕ) : ∀ (n : ℕ) {y : Ainf l},
    (l : Ainf l) ^ m * y ∈ Iw ϖ ^ (n + m) → y ∈ Iw ϖ ^ n := by
  induction m with
  | zero => intro n y h; simpa using h
  | succ m ih =>
    intro n y h
    refine mem_of_l_mul hϖ n (ih (n + 1) ?_)
    rw [← mul_assoc, ← pow_succ, show n + 1 + m = n + (m + 1) by omega]
    exact h

end GlobalTheory.AcrisMuBound

namespace GlobalTheory.AcrisMuBound

variable {l : ℕ} [hl : Fact l.Prime]

theorem mem_of_theta {ϖ : OCb l} (hϖ : ϖ.untilt = (l : Per.OC l)) {x : Ainf l} (hx : Per.θ l x = 0) :
    x ∈ Ideal.span {(l : Ainf l)} ⊔ Ideal.span {WittVector.teichmuller l ϖ} := by
  obtain ⟨z, hz⟩ := l_dvd_sub_teich x
  have h1 : (WittVector.constantCoeff x).untilt = -((l : Per.OC l) * Per.θ l z) := by
    have := congrArg (Per.θ l) hz
    rw [map_sub, hx, WittVector.fontaineTheta_teichmuller, map_mul, map_natCast] at this
    linear_combination -this
  obtain ⟨c, hc⟩ : ϖ ∣ WittVector.constantCoeff x :=
    GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd (by rw [hϖ, h1]; exact (Dvd.intro _ rfl).neg_right)
  have h2 : x = (l : Ainf l) * z + WittVector.teichmuller l ϖ * WittVector.teichmuller l c := by
    rw [← map_mul, ← hc, ← hz]; ring
  rw [h2]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
    (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

theorem pow_le_Iw (ϖ : OCb l) :
    (Ideal.span {(l : Ainf l)} ⊔ Ideal.span {WittVector.teichmuller l ϖ}) ^ (l - 1) ≤ Iw ϖ := by
  have h2 := hl.out.two_le
  have h := sup_pow_le (Ideal.span {(l : Ainf l)}) (Ideal.span {WittVector.teichmuller l ϖ}) (l - 2)
  rw [show l - 2 + 1 = l - 1 by omega, Ideal.span_singleton_pow] at h
  exact h.trans (sup_le_sup_right Ideal.mul_le_left _)

def Qs (ϖ : OCb l) : Subalgebra (Per.Ainf l) (Per.AinfP l) where
  carrier := {z | ∃ m : ℕ, ∃ a ∈ Iw ϖ ^ m, (l : Per.AinfP l) ^ m * z = algebraMap _ _ a}
  mul_mem' := by
    rintro z w ⟨m, a, ha, hz⟩ ⟨k, b, hb, hw⟩
    exact ⟨m + k, a * b, by rw [pow_add]; exact Ideal.mul_mem_mul ha hb, by
      rw [map_mul, ← hz, ← hw]; ring⟩
  add_mem' := by
    rintro z w ⟨m, a, ha, hz⟩ ⟨k, b, hb, hw⟩
    refine ⟨m + k, a * (l : Ainf l) ^ k + (l : Ainf l) ^ m * b, ?_, ?_⟩
    · rw [pow_add]
      exact Ideal.add_mem _ (Ideal.mul_mem_mul ha (Ideal.pow_mem_pow (l_mem_Iw ϖ) k))
        (Ideal.mul_mem_mul (Ideal.pow_mem_pow (l_mem_Iw ϖ) m) hb)
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, ← hz, ← hw]; ring
  algebraMap_mem' r := ⟨0, r, by simp, by simp⟩

theorem dividedPower_mem_pt {ϖ : OCb l} (hϖ : ϖ.untilt = (l : Per.OC l)) (x : Per.Ainf l) (k : ℕ)
    (y : Per.AinfP l) (hx : Per.θ l x = 0)
    (hk : ((k.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) x ^ k) :
    y ∈ Qs ϖ := by
  have hxI := mem_of_theta hϖ hx
  have he : (l - 1) * k.factorial.factorization l ≤ k := by
    have := sub_one_mul_padicValNat_factorial (p := l) k
    rw [← Nat.factorization_def _ hl.out] at this
    omega
  set e := k.factorial.factorization l
  set r := k.factorial / l ^ e
  have hkr : l ^ e * r = k.factorial := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hr : ¬ l ∣ r := Nat.not_dvd_ordCompl hl.out k.factorial_ne_zero
  have hru : IsUnit (r : ℤ_[l]) := PadicInt.isUnit_iff.2
    (PadicInt.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hr))
  obtain ⟨w, hw⟩ := hru.exists_left_inv
  refine ⟨e, algebraMap ℤ_[l] (Ainf l) w * x ^ k, ?_, ?_⟩
  · refine Ideal.mul_mem_left _ _ ?_
    have h1 : x ^ k ∈ (Ideal.span {(l : Ainf l)} ⊔ Ideal.span {WittVector.teichmuller l ϖ}) ^ ((l - 1) * e) :=
      Ideal.pow_le_pow_right he (Ideal.pow_mem_pow hxI k)
    rw [pow_mul] at h1
    exact Ideal.pow_right_mono (pow_le_Iw ϖ) e h1
  · have h1 : (algebraMap ℤ_[l] (Ainf l) w) * (r : Ainf l) = 1 := by
      rw [← map_natCast (algebraMap ℤ_[l] (Ainf l)), ← map_mul, hw, map_one]
    have h2 := congrArg (algebraMap (Per.Ainf l) (Per.AinfP l)) h1
    rw [map_mul, map_one, map_natCast] at h2
    rw [map_mul, map_pow, ← hk, ← hkr]
    push_cast
    linear_combination (-(l : Per.AinfP l) ^ e * y) * h2

theorem acris0_le (hl2 : 2 ≤ l) {ϖ : OCb l} (hϖ : ϖ.untilt = (l : Per.OC l)) : Per.Acris0 l ≤ Qs ϖ :=
  GlobalTheory.RingIface.Acris0_le_of_dividedPowers l _ (dividedPower_mem_pt hϖ)

theorem exists_of_dvd {n : ℕ} {y : Ainf l} (h : (l : Per.Acris l) ^ n ∣ ainfToAcris l y) :
    ∃ z ∈ Per.Acris0 l, (l : Per.AinfP l) ^ n * z = algebraMap (Per.Ainf l) (Per.AinfP l) y := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  have h3 : ainfToAcris l y =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) y) :=
    GlobalTheory.RingIface.tower l y
  have hw' := congrArg e hw
  rw [h3, he, map_mul, map_pow, map_natCast] at hw'
  have h1 := congrArg (AdicCompletion.evalₐ (Ideal.span {(l : Per.Acris0 l)}) n) hw'
  rw [map_mul, map_pow, map_natCast] at h1
  have h0 : ((l : Per.Acris0 l ⧸ Ideal.span {(l : Per.Acris0 l)} ^ n)) ^ n = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n
  have h2 : algebraMap (Per.Ainf l) (Per.Acris0 l) y ∈ Ideal.span {(l : Per.Acris0 l)} ^ n := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change AdicCompletion.evalₐ _ n (AdicCompletion.of (Ideal.span {(l : Per.Acris0 l)}) _
      (algebraMap (Per.Ainf l) (Per.Acris0 l) y)) = _ at h1
    rw [h0, zero_mul, AdicCompletion.evalₐ_of] at h1
    exact h1
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h2
  obtain ⟨z, hz⟩ := h2
  refine ⟨z, z.2, ?_⟩
  have := congrArg Subtype.val hz
  simpa [mul_comm] using this

end GlobalTheory.AcrisMuBound

namespace GlobalTheory.AcrisMuBound

variable {l : ℕ} [hl : Fact l.Prime]

theorem ne_zero_of_untilt {ϖ : OCb l} (hϖ : ϖ.untilt = (l : Per.OC l)) : ϖ ≠ 0 := by
  rintro rfl
  have h1 : (l : Per.OC l) ^ 2 = l := by rw [← hϖ, ← map_pow, zero_pow two_ne_zero]
  have h2 : ((l : ℕ) : ℂ_[l]) * (l : ℂ_[l]) = (l : ℂ_[l]) * 1 := by
    have := congrArg Subtype.val h1
    push_cast at this
    rw [mul_one, ← pow_two]; exact this
  have h3 := mul_left_cancel₀ (GlobalTheory.RingBasics.p_ne_zero (p := l)) h2
  exact hl.out.one_lt.ne' (by exact_mod_cast h3)

theorem pow_dvd_cc (hl2 : 2 ≤ l) {ϖ : OCb l} (hϖ : ϖ.untilt = (l : Per.OC l)) {n : ℕ} {y : Ainf l}
    (h : (l : Per.Acris l) ^ n ∣ ainfToAcris l y) : ϖ ^ ((l - 1) * n) ∣ WittVector.constantCoeff y := by
  obtain ⟨z, hz0, hz⟩ := exists_of_dvd h
  obtain ⟨m, a, ha, hza⟩ := acris0_le hl2 hϖ hz0
  have hinj : Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) :=
    IsLocalization.injective (Per.AinfP l) (powers_le_nonZeroDivisors_of_noZeroDivisors l_ne_zero_ainf)
  have h1 : (l : Ainf l) ^ m * y = (l : Ainf l) ^ n * a := by
    apply hinj
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, ← hz, ← hza]
    ring
  have h2 : y ∈ Iw ϖ ^ n := by
    refine mem_of_l_pow_mul (ne_zero_of_untilt hϖ) m n ?_
    rw [h1, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (l_mem_Iw ϖ) n) ha
  have h3 := Ideal.mem_map_of_mem (WittVector.constantCoeff (p := l) (R := OCb l)) h2
  have h4 : Ideal.map (WittVector.constantCoeff (p := l) (R := OCb l)) (Iw ϖ) ≤ Ideal.span {ϖ ^ (l - 1)} := by
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      cc_natCast_l, map_pow, cc_teich, Ideal.span_singleton_eq_bot.2 rfl, bot_sup_eq]
  rw [Ideal.map_pow] at h3
  have h5 := Ideal.pow_right_mono h4 n h3
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← pow_mul] at h5
  exact h5

end GlobalTheory.AcrisMuBound

namespace GlobalTheory.AcrisMuBound

variable {l : ℕ} [hl : Fact l.Prime]

theorem tilt_bound (hl2 : l ≠ 2) {ε ϖ : OCb l} (hε : IsEps ε) (hϖ : ϖ.untilt = (l : Per.OC l)) {N j : ℕ}
    (h : ϖ ^ N ∣ (ε - 1) ^ j) : (l - 1) * N ≤ l * j := by
  obtain ⟨hε1, δ, hδ, hδ1⟩ := hε
  have hl3 : 3 ≤ l := by have := hl.out.two_le; omega
  set ζ : ℂ_[l] := ((δ.untilt : Per.OC l) : ℂ_[l]) with hζ
  have hζl : ζ ^ l = 1 := by
    have h1 : δ.untilt ^ l = 1 := by rw [← map_pow, hδ, hε1]
    have := congrArg Subtype.val h1
    push_cast at this
    exact this
  have hζ1 : ζ ≠ 1 := fun h1 => hδ1 (Subtype.ext (by rw [OneMemClass.coe_one]; exact h1))
  have hprim : IsPrimitiveRoot ζ l := by
    have := IsPrimitiveRoot.orderOf ζ; rwa [orderOf_eq_prime hζl hζ1] at this
  have ha : ‖ζ - 1‖ ^ (l - 1) = ‖((l : ℕ) : ℂ_[l])‖ := by
    have := GlobalTheory.CycTrace.norm_sub_one_pow_totient (K := ℂ_[l]) l 0 ζ (by simpa using hprim)
    simpa [Nat.totient_prime hl.out] using this
  set a := ‖ζ - 1‖
  set b := ‖((l : ℕ) : ℂ_[l])‖
  have hb0 : 0 < b := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  have hb1 : b < 1 := GlobalTheory.RingBasics.norm_p_lt
  have ha0 : 0 ≤ a := norm_nonneg _
  have ha1 : a < 1 := by
    by_contra hc
    have : 1 ≤ a ^ (l - 1) := one_le_pow₀ (not_lt.1 hc)
    linarith
  have hba : b < a := by
    have h1 : a ^ (l - 2) < 1 := pow_lt_one₀ ha0 ha1 (by omega)
    have h2 : a ^ (l - 1) = a * a ^ (l - 2) := by
      rw [← pow_succ']; congr 1; omega
    have ha0' : 0 < a := by
      rcases ha0.lt_or_eq with h | h
      · exact h
      · rw [← h, zero_pow (by omega)] at ha; linarith
    nlinarith

  obtain ⟨t, ht⟩ := GlobalTheory.TiltAbs.untilt_add (δ - 1) 1
  rw [sub_add_cancel, map_one] at ht
  set d : ℂ_[l] := (((δ - 1).untilt : Per.OC l) : ℂ_[l])
  have hd : a ≤ ‖d‖ := by
    have h1 : ζ - 1 = d + (l : ℂ_[l]) * ((t : Per.OC l) : ℂ_[l]) := by
      have := congrArg Subtype.val ht
      push_cast at this
      rw [hζ, this]; ring
    have h2 : ‖(l : ℂ_[l]) * ((t : Per.OC l) : ℂ_[l])‖ < a := by
      rw [norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (GlobalTheory.TiltAbs.norm_le_one t)) hba
    have h3 : a ≤ max ‖d‖ ‖(l : ℂ_[l]) * ((t : Per.OC l) : ℂ_[l])‖ := by
      have := IsUltrametricDist.norm_add_le_max d ((l : ℂ_[l]) * ((t : Per.OC l) : ℂ_[l]))
      rw [← h1] at this
      exact this
    rcases le_max_iff.1 h3 with h | h
    · exact h
    · exact absurd h (not_le.2 h2)

  have hεδ : ε - 1 = (δ - 1) ^ l := by rw [sub_pow_char, one_pow, hδ]
  obtain ⟨c, hc⟩ := map_dvd (PreTilt.untilt (O := Per.OC l) (p := l)) h
  rw [map_pow, map_pow, hϖ, hεδ, map_pow] at hc
  have hc' := congrArg (fun z : Per.OC l => ‖(z : ℂ_[l])‖) hc
  push_cast at hc'
  rw [norm_mul, norm_pow, norm_pow, norm_pow] at hc'
  have h4 : ‖d‖ ^ (l * j) ≤ b ^ N := by
    rw [pow_mul]
    rw [hc']
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (GlobalTheory.TiltAbs.norm_le_one c)
  have h5 : a ^ (l * j) ≤ b ^ N := (pow_le_pow_left₀ ha0 hd _).trans h4
  have h6 : b ^ (l * j) ≤ b ^ ((l - 1) * N) := by
    calc b ^ (l * j) = (a ^ (l - 1)) ^ (l * j) := by rw [ha]
      _ = (a ^ (l * j)) ^ (l - 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (b ^ N) ^ (l - 1) := pow_le_pow_left₀ (pow_nonneg ha0 _) h5 _
      _ = b ^ ((l - 1) * N) := by rw [← pow_mul, mul_comm]
  exact (pow_le_pow_iff_right_of_lt_one₀ hb0 hb1).1 h6

end GlobalTheory.AcrisMuBound

namespace GlobalTheory.AcrisMuBound

theorem main : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ ε : OCb l, IsEps ε → ∀ (j n : ℕ) (x : ℤ_[l]), x ≠ 0 → (l : Per.Acris l) ^ n ∣ ainfToAcris l (muOf ε ^ j * algebraMap ℤ_[l] (Ainf l) x) → (l - 1) * n ≤ (l - 1) * x.valuation + 2 * j := by
  intro l hl hl2 ε hε j n x hx h
  have hl2' : 2 ≤ l := hl.out.two_le
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l (l : Per.OC l)
  set u := PadicInt.unitCoeff hx
  set v := x.valuation
  have hxu : algebraMap ℤ_[l] (Ainf l) x = (l : Ainf l) ^ v * algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l]) := by
    conv_lhs => rw [PadicInt.unitCoeff_spec hx]
    rw [map_mul, map_pow, map_natCast, mul_comm]
  set y := muOf ε ^ j * algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l])
  rcases le_or_gt n v with hnv | hnv
  · have := Nat.mul_le_mul_left (l - 1) hnv
    omega
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hnv.le
  have h2 : (l : Per.Acris l) ^ n' ∣ ainfToAcris l y := by
    obtain ⟨w, hw⟩ := h
    refine ⟨w, ?_⟩
    have h3 : ((l ^ v : ℕ) : Per.Acris l) * (ainfToAcris l y - (l : Per.Acris l) ^ n' * w) = 0 := by
      rw [hxu, mul_left_comm, map_mul, map_pow, map_natCast] at hw
      push_cast
      rw [mul_sub, hw]
      ring
    exact sub_eq_zero.1 (acris_nat_cancel (pow_ne_zero _ hl.out.ne_zero) h3)
  have h4 := pow_dvd_cc hl2' hϖ h2
  have h5 : WittVector.constantCoeff y = (ε - 1) ^ j * WittVector.constantCoeff (algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l])) := by
    simp only [y, muOf, map_mul, map_pow, map_sub, map_one, cc_teich]
  have hu : IsUnit (WittVector.constantCoeff (algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l]))) :=
    (u.isUnit.map _).map _
  rw [h5, hu.dvd_mul_right] at h4
  have h6 := tilt_bound hl2 hε hϖ h4
  have h7 : l ≤ 2 * (l - 1) := by omega
  have h8 : (l - 1) * ((l - 1) * n') ≤ (l - 1) * (2 * j) := by
    calc (l - 1) * ((l - 1) * n') ≤ l * j := h6
      _ ≤ 2 * (l - 1) * j := Nat.mul_le_mul_right j h7
      _ = (l - 1) * (2 * j) := by ring
  have h9 := Nat.le_of_mul_le_mul_left h8 (by omega)
  rw [mul_add]
  omega

end GlobalTheory.AcrisMuBound
