import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Taylor
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorWp
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorSigma

noncomputable section
open Filter Topology

namespace Formalism.L2.Th1.F

namespace ThetaZeroTaylorLemmas

open PowerSeries in
lemma derivative_prim (f : PowerSeries ℂ) : derivative ℂ (B.prim f) = f := B.dz_prim f

open PowerSeries in

lemma sigS_add_const (Q : PowerSeries ℂ) (s : ℂ) :
    B.sigS (Q + C s) = -B.prim (B.prim Q) + -(C (s / 2) * X ^ 2) := by
  have h1 : derivative ℂ (C (s / 2) * X ^ 2 : PowerSeries ℂ) = C s * X := by
    have hs : (C s : PowerSeries ℂ) = C (s / 2) * 2 := by
      rw [show (2 : PowerSeries ℂ) = C 2 from (map_ofNat C 2).symm, ← map_mul]
      congr 1
      ring
    rw [Derivation.leibniz, derivative_C, Derivation.leibniz_pow, derivative_X, hs]
    simp only [smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, mul_one, Nat.cast_ofNat]
    ring
  have h2 : derivative ℂ (C s * X : PowerSeries ℂ) = C s := by
    rw [Derivation.leibniz, derivative_C, derivative_X]
    simp
  refine derivative.ext (derivative.ext ?_ ?_) ?_
  · rw [B.sigS, map_neg, map_neg, derivative_prim, derivative_prim, map_add, map_add, map_neg,
      map_neg, map_neg, map_neg, derivative_prim, derivative_prim, h1, h2, neg_add]
  · rw [B.sigS, map_neg, map_neg, derivative_prim, map_add, map_neg, map_neg, derivative_prim, h1]
    simp [B.constantCoeff_prim]
  · simp [B.sigS, B.constantCoeff_prim]

def v (L : PeriodPair) (t z : ℂ) : ℂ := wZeta L (z + t) - wZeta L t - s2 L * z

lemma v_zero (L : PeriodPair) (t : ℂ) : v L t 0 = 0 := by simp [v]

lemma isOpen_dom (L : PeriodPair) (t : ℂ) : IsOpen {z : ℂ | z + t ∉ L.lattice} :=
  L.isClosed_lattice.isOpen_compl.preimage (continuous_add_const t)

lemma dom_mem_nhds (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) :
    {z : ℂ | z + t ∉ L.lattice} ∈ 𝓝 (0 : ℂ) :=
  (isOpen_dom L t).mem_nhds (by simpa using ht)

lemma hasDerivAt_v (L : PeriodPair) {t z : ℂ} (h : z + t ∉ L.lattice) :
    HasDerivAt (v L t) (-(L.weierstrassP (z + t)) - s2 L) z := by
  have h1 : HasDerivAt (fun x => wZeta L (x + t)) (-(L.weierstrassP (z + t))) z :=
    (zetaHasDeriv L (z + t) h).comp_add_const z t
  have h2 : HasDerivAt (fun x : ℂ => s2 L * x) (s2 L * 1) z := (hasDerivAt_id z).const_mul (s2 L)
  rw [mul_one] at h2
  exact (h1.sub_const (wZeta L t)).sub h2

lemma analyticAt_v (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) : AnalyticAt ℂ (v L t) 0 :=
  DifferentiableOn.analyticAt
    (fun _ hz => (hasDerivAt_v L hz).differentiableAt.differentiableWithinAt) (dom_mem_nhds L ht)

lemma ode_th (L : PeriodPair) {ω₀ : ℂ} (hω : ω₀ ∈ L.lattice) (ht : ω₀ / 2 ∉ L.lattice) :
    deriv (th0 L (ω₀ / 2)) =ᶠ[𝓝 0] fun z => v L (ω₀ / 2) z * th0 L (ω₀ / 2) z := by
  filter_upwards [dom_mem_nhds L ht] with z hz
  exact (th0LogDeriv L ω₀ z hω ht hz).deriv

lemma ode_v (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) (h2t : 2 * t ∈ L.lattice) :
    (fun z => (1 + z * z * L.weierstrassPExcept 0 z + -(L.weierstrassP t) * (z * z))
        * (deriv (v L t) z + L.weierstrassP t + s2 L))
      =ᶠ[𝓝 0] fun z => -(3 * L.weierstrassP t ^ 2 - L.g₂ / 4) * (z * z) := by
  filter_upwards [dom_mem_nhds L ht, L.compl_lattice_sdiff_singleton_mem_nhds 0] with z h1 h2
  rw [(hasDerivAt_v L h1).deriv]
  by_cases h0 : z = 0
  · simp only [h0, zero_add, mul_zero, zero_mul, add_zero, one_mul]
    ring
  have hzl : z ∉ L.lattice := fun h => h2 ⟨h, h0⟩
  have hs := halfShift L t z ht h2t hzl h1
  have h5 := L.weierstrassPExcept_add 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero] at h5
  have hz2 : z * z * (1 / z ^ 2) = 1 := by field_simp
  linear_combination (-(z * z)) * hs - (z * z) * (L.weierstrassP (z + t) - L.weierstrassP t) * h5
    + (L.weierstrassP (z + t) - L.weierstrassP t) * hz2

end ThetaZeroTaylorLemmas

open ThetaZeroTaylorLemmas TaylorWp in

theorem taylor_even_theta : TaylorTh0 := by
  intro L ω₀ hω ht
  have hr := taylor_ring
  set t := ω₀ / 2 with htdef
  have h2t : 2 * t ∈ L.lattice := by
    have : 2 * t = ω₀ := by rw [htdef]; ring
    rwa [this]
  set e := L.weierstrassP t with he
  set κ := 3 * e ^ 2 - L.g₂ / 4 with hκ
  obtain ⟨hdiff, h0, -⟩ := th0Basic L ω₀ hω ht
  have hθ : AnalyticAt ℂ (th0 L t) 0 := hdiff.analyticAt 0
  have hv : AnalyticAt ℂ (v L t) 0 := analyticAt_v L ht
  have eU : PowerSeries.derivative ℂ (taylor0 (th0 L t)) = taylor0 (v L t) * taylor0 (th0 L t) := by
    rw [← Taylor.taylor0_deriv, ← Taylor.taylor0_mul hv hθ]
    exact Taylor.taylor0_congr (ode_th L hω ht)
  have Tid := T.id hr
  have Tzz := T.mul hr Tid Tid
  have Tp : T (L.weierstrassPExcept 0) (pSeries L) := ⟨TaylorSigmaUniqueness.analyticAt_pExcept L, rfl⟩
  have Tdv : T (deriv (v L t)) (PowerSeries.derivative ℂ (taylor0 (v L t))) :=
    ⟨hv.deriv, Taylor.taylor0_deriv _⟩
  have TL := T.mul hr (T.add hr (T.add hr (T.const hr 1) (T.mul hr Tzz Tp)) (T.mul hr (T.const hr (-e)) Tzz))
    (T.add hr (T.add hr Tdv (T.const hr e)) (T.const hr (s2 L)))
  have TR := T.mul hr (T.const hr (-κ)) Tzz
  have hE := TL.2.symm.trans ((Taylor.taylor0_congr (ode_v L ht h2t)).trans TR.2)
  rw [map_one, map_neg, map_neg] at hE
  set V := taylor0 (v L t) with hV
  set P := pSeries L with hP
  have hD0 : PowerSeries.constantCoeff
      (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e * PowerSeries.X ^ 2 : PowerSeries ℂ) ≠ 0 := by
    simp
  have hD := PowerSeries.mul_inv_cancel _ hD0
  have eV : PowerSeries.derivative ℂ V
      = -(PowerSeries.C e + PowerSeries.C κ * B.wOf e P + PowerSeries.C (s2 L)) := by
    rw [B.wOf]
    generalize (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e * PowerSeries.X ^ 2 : PowerSeries ℂ)⁻¹ = Di
      at hD ⊢
    linear_combination Di * hE
      - (PowerSeries.derivative ℂ V + PowerSeries.C e + PowerSeries.C (s2 L)) * hD
  have key := TaylorSigmaUniqueness.formal_unique
    (PowerSeries.C e + PowerSeries.C κ * B.wOf e P + PowerSeries.C (s2 L)) (taylor0 (th0 L t)) V
    (by rw [eV, mul_neg]) (by rw [TaylorSigmaUniqueness.constantCoeff_taylor0, v_zero])
    (by rw [eU]) (by rw [TaylorSigmaUniqueness.constantCoeff_taylor0, h0])
  rw [key, sigS_add_const, B.sigma1, B.sigmaOneSeries]
  refine B.fExp_add ?_ ?_
  · have : PowerSeries.constantCoeff
        (-B.prim (B.prim (PowerSeries.C e + PowerSeries.C κ * B.wOf e P)) : PowerSeries ℂ) = 0 := by
      rw [map_neg, B.constantCoeff_prim, neg_zero]
    exact this
  · have : PowerSeries.constantCoeff
        (-(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2) : PowerSeries ℂ) = 0 := by simp
    exact this

end Formalism.L2.Th1.F
