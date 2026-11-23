import Mathlib
import Formalism.LocalToGlobal.KernelLattices.MuProd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PenultimateKernelDiamondInvariant
import Formalism.LocalToGlobal.Columns.ReductionExistsInLatticeStabilizerHolds

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section LocCharMul

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem ml_ne_zero {u : E} (h : IsUnit (redP P u)) : u ≠ 0 := by
  rintro rfl
  rw [redP_zero] at h
  exact not_isUnit_zero h

theorem ml_int_inv {u : E} (h : IsUnit (redP P u)) : IntAt P u⁻¹ := yIntAt_inv (intAt_of_isUnit h) h.ne_zero

theorem ml_unit_inv {u : E} (h : IsUnit (redP P u)) : IsUnit (redP P u⁻¹) :=
  isUnit_reduction_of_integralAt_inv (ml_int_inv h) (by rw [inv_inv]; exact intAt_of_isUnit h) (inv_ne_zero (ml_ne_zero h))

theorem ml_unit_mul {u w : E} (h : IsUnit (redP P u)) (h' : IsUnit (redP P w)) : IsUnit (redP P (u * w)) := by
  rw [reduction_mul (intAt_of_isUnit h) (intAt_of_isUnit h')]
  exact h.mul h'

theorem ml_qpow_pos {q : ℕ} (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (k : ℕ) : ¬ IsUnit (redP P ((q : E) ^ (k + 1))) := by
  rw [(ocbA_pow_red hq k).2]
  exact not_isUnit_zero

theorem ml_qpow_unit {q : ℕ} (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (k : ℤ) (h : IsUnit (redP P ((q : E) ^ k))) : k = 0 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -((m : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    have h2 := ml_unit_inv h
    rw [hm, zpow_neg, inv_inv] at h2
    have e : (q : E) ^ ((m : ℤ) + 1) = (q : E) ^ (m + 1) := by
      rw [← zpow_natCast]; congr 1
    rw [e] at h2
    exact ml_qpow_pos hq m h2
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = (m : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
    have e : (q : E) ^ ((m : ℤ) + 1) = (q : E) ^ (m + 1) := by
      rw [← zpow_natCast]; congr 1
    rw [hm, e] at h
    exact ml_qpow_pos hq m h

theorem isUnit_div_pow_valuation (q : ℕ) (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (a : E) (ha : a ≠ 0) :
    IsUnit (redP P (a / (q : E) ^ LocE.vP P q a)) :=
  Classical.epsilon_spec (exists_isUnit_div P q hq hu a ha)

theorem valuation_eq_of_isUnit_div_pow (q : ℕ) (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (a : E) (z : ℤ)
    (h : IsUnit (redP P (a / (q : E) ^ z))) : LocE.vP P q a = z := by
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_div] at h
    exact ml_ne_zero h rfl
  have h1 := isUnit_div_pow_valuation q hq hu a ha
  have h2 := ml_unit_mul h (ml_unit_inv h1)
  have e : a / (q : E) ^ z * (a / (q : E) ^ LocE.vP P q a)⁻¹ = (q : E) ^ (LocE.vP P q a - z) := by
    rw [zpow_sub₀ hq0]
    have hz : (q : E) ^ z ≠ 0 := zpow_ne_zero _ hq0
    have hn : (q : E) ^ LocE.vP P q a ≠ 0 := zpow_ne_zero _ hq0
    field_simp
  rw [e] at h2
  have := ml_qpow_unit hq _ h2
  omega

theorem valuation_mul₂ (q : ℕ) (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (a b : E) (ha : a ≠ 0) (hb : b ≠ 0) :
    LocE.vP P q (a * b) = LocE.vP P q a + LocE.vP P q b := by
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  apply valuation_eq_of_isUnit_div_pow q hq hu
  have e : a * b / (q : E) ^ (LocE.vP P q a + LocE.vP P q b) = a / (q : E) ^ LocE.vP P q a * (b / (q : E) ^ LocE.vP P q b) := by
    rw [zpow_add₀ hq0, mul_div_mul_comm]
  rw [e]
  exact ml_unit_mul (isUnit_div_pow_valuation q hq hu a ha) (isUnit_div_pow_valuation q hq hu b hb)

variable {K : Type} [Field K]

theorem ml_locChar_mul (q : ℕ) (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (cq : K) (hcq : cq ≠ 0)
    (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a b : E) (ha : a ≠ 0) (hb : b ≠ 0) :
    LocE.locChar q cq χ (a * b) = LocE.locChar q cq χ a * LocE.locChar q cq χ b := by
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  have hB := isUnit_div_pow_valuation q hq hu b hb
  unfold LocE.locChar
  rw [valuation_mul₂ q hq hu a b ha hb, zpow_add₀ hcq, zpow_add₀ hq0, mul_div_mul_comm,
    unitV_mul_unit χ (intAt_of_isUnit hB) (ml_int_inv hB) (ml_ne_zero hB)]
  ring

end LocCharMul

section Ord

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem ml_ordDet_gmap (Q : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (hN : Submodule.IsLattice E N) (γ : Sp E n ≃ₗ[E] Sp E n) :
    ordDet Q (gmap γ N) = ordE Q ((LinearEquiv.det γ : Eˣ) : E) + ordDet Q N := by
  obtain ⟨f, hf⟩ := exists_frameD Q hN
  have hf' : ∀ x, (γ * f) x ∈ localization₂ Q.asIdeal (gmap γ N) ↔ x ∈ stdAt E n Q := by
    intro x
    rw [mem_localization_gmap]
    show γ.symm (γ (f x)) ∈ _ ↔ _
    rw [LinearEquiv.symm_apply_apply]
    exact hf x
  rw [ordDet_eq_of_frame Q (gmap γ N) (γ * f) hf', ordDet_eq_of_frame Q N f hf, map_mul, Units.val_mul,
    ordE_mul Q (Units.ne_zero _) (Units.ne_zero _)]

theorem ml_ordE_finite (z : E) (hz : z ≠ 0) : {Q : HeightOneSpectrum (𝓞 E) | ordE Q z ≠ 0}.Finite := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) z
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hz
    rw [map_zero, zero_div]
  have hsE : algebraMap (𝓞 E) E s ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).2 hs0
  have hrE : algebraMap (𝓞 E) E r ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).2 hr0
  have hI : Ideal.span {r * s} ≠ (0 : Ideal (𝓞 E)) := by
    intro h0
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h0
    exact (mul_ne_zero hr0 hs0) h0
  refine (Ideal.finite_factors hI).subset ?_
  intro Q hQ
  by_contra hc
  apply hQ
  have hm : r * s ∉ Q.asIdeal := fun hmem => hc (Ideal.dvd_span_singleton.2 hmem)
  have hrQ : r ∉ Q.asIdeal := fun hmem => hm (Ideal.mul_mem_right _ _ hmem)
  have hsQ : s ∉ Q.asIdeal := fun hmem => hm (Ideal.mul_mem_left _ _ hmem)
  refine ordE_eq_zero hz ⟨r, s, hsQ, ?_⟩ ⟨s, r, hrQ, ?_⟩
  · rw [mul_div_cancel₀ _ hsE]
  · rw [inv_div, mul_div_cancel₀ _ hrE]

end Ord

section Ratio

variable {X : Fields} {n : ℕ}

open Classical in

def zFac (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (z : X.E) (v : HeightOneSpectrum (𝓞 X.F)) : X.K :=
  if ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal then 1 else ((mU (sel v) ^ ordE (sel v) z : X.Kˣ) : X.K)

theorem ml_zFac_support {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} (hsel : IsSel X sel) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (z : X.E) (hz : z ≠ 0) : (Function.mulSupport (zFac sel SB mU z)).Finite := by
  refine Set.Finite.subset (Set.Finite.preimage (sel_injective hsel).injOn (ml_ordE_finite z hz)) ?_
  intro v hv
  by_contra hc
  apply hv
  have h0 : ordE (sel v) z = 0 := by
    by_contra h
    exact hc h
  unfold zFac
  split_ifs
  · rfl
  · rw [h0]
    simp

theorem ml_muOff_gmap {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} (hsel : IsSel X sel) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)) (hN : IsSdLat N) :
    muOff sel SB mU (gmap γ N) = (∏ᶠ v, zFac sel SB mU ((LinearEquiv.det γ : X.Eˣ) : X.E) v) * muOff sel SB mU N := by
  rw [muOff_eq, muOff_eq, ← finprod_mul_distrib (ml_zFac_support hsel SB mU _ (Units.ne_zero _))
    (muFac_support hsel SB mU (frame_det_unit_almost_all_primes n) N hN)]
  refine finprod_congr fun v => ?_
  unfold muFac zFac
  by_cases hv : ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal
  · rw [if_pos hv, if_pos hv, if_pos hv, one_mul]
  · rw [if_neg hv, if_neg hv, if_neg hv, ← Units.val_mul, ← zpow_add, ml_ordDet_gmap (sel v) N hN.1 γ]

theorem ml_ratio {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} (hsel : IsSel X sel) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
    (hmul : ∀ (P : SB) (a b : X.E), a ≠ 0 → b ≠ 0 → mI P (a * b) = mI P a * mI P b)
    (γ : UF X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)) (hN : IsSdLat N) (fr : Frs X.E n SB) :
    muInvDet sel SB mU mI (gmap γ.1 N) (fun P => γ.1 * fr P) =
      ((∏ᶠ v, zFac sel SB mU ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) v) * ∏ P : SB, mI P ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) *
        muInvDet sel SB mU mI N fr := by
  unfold muInvDet
  rw [ml_muOff_gmap hsel SB mU γ.1 N hN]
  have e : ∏ P : SB, mI P ((LinearEquiv.det (γ.1 * fr P) : X.Eˣ) : X.E) =
      (∏ P : SB, mI P ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) * ∏ P : SB, mI P ((LinearEquiv.det (fr P) : X.Eˣ) : X.E) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [map_mul, Units.val_mul, hmul P _ _ (Units.ne_zero _) (Units.ne_zero _)]
  rw [e]
  ring

end Ratio

end Formalism.L2.Ker
