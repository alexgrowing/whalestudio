import Formalism.HermitianCurvature.StatementJ

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open MeasureTheory Formalism.H
open scoped FourierTransform ComplexConjugate nonZeroDivisors

namespace Formalism.FourierDecayAlt.P

namespace Jx4

theorem rd_pos (E : Type) [Field E] [NumberField E] [IsCMField E] : 0 < S6.rd E := by
  have h : (0 : ℝ) < ((|NumberField.discr E| : ℤ) : ℝ) := by
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero E)
  unfold S6.rd
  first
    | exact Real.rpow_pos_of_pos h _
    | exact Real.rpow_pos h _

end Jx4

theorem fourier_transform_at_zero : Formalism.FourierDecayAlt.J.TransformAtZero := by
  intro V _ _ _ _ _ φ
  first
    | (simp [Real.fourier_eq]; done)
    | (simp [Real.fourierIntegral_eq']; done)
    | (simp [Real.fourierIntegral_eq]; done)
    | (simp [Real.fourierIntegral, VectorFourier.fourierIntegral]; done)
    | (simp [FourierTransform.fourier, Real.fourierIntegral, VectorFourier.fourierIntegral]; done)
    | (simp [VectorFourier.fourierIntegral]; done)

theorem poisson_level_joint : Formalism.FourierDecayAlt.J.PoissonStepJoint := by
  intro hF hJ E W _ D V _ _ _ _ _ ι _ π hπ Λ _ _ emb dmap hFr hW
  intro ε hε i hi1 hi2 w Y hY κ hκ t₀ B hB S hS
  obtain ⟨φ, Cφ, hc, hb, hnn, hdiag, hhat⟩ := hW ε hε i hi1 hi2 w Y hY κ hκ
  obtain ⟨hinj, hmem, hd0, hdual⟩ := hFr i hi1 hi2
  have key := hJ hF V ι π hπ (Λ i) E (emb i) (dmap i) (D.La i 1) (D.Lad i) φ Cφ
    (D.Nhat ε i w Y κ) hinj hmem hd0 hdual hc hb hnn hhat t₀ B hB S (fun t ht => (hS t ht).2)
  refine Eq.trans_le ?_ key
  exact Finset.sum_congr rfl fun t ht => hdiag t (hS t ht).1

theorem poisson_joint_first_reduction : Formalism.FourierDecayAlt.J.PoissonJointTA := by
  intro hF hJ E _ _ D H _ _ W _ Φ tr i V _ _ _ _ _ ι _ π hπ Λ _ _ emb dmap hinj hmem hd0 hdual hW
  intro w Hd kap hHd hk t0 T hT B hB
  obtain ⟨φ, Cφ, hc, hb, hnn, hdiag, hhat⟩ := hW w Hd kap hHd hk
  have key := hJ hF V ι π hπ Λ E emb dmap (D.La i 1) (D.Lv i) φ Cφ (tr w Hd kap)
    hinj hmem hd0 hdual hc hb hnn hhat t0 B hB T (fun t ht => (hT t ht).2)
  refine Eq.trans_le ?_ key
  exact Finset.sum_congr rfl fun t ht => hdiag t (hT t ht).1

theorem poisson_forms_agree : Formalism.FourierDecayAlt.J.PoissonAgree := by
  intro hA hT E W _ _ _ D H _ _ Φ ε i hε hi1 hi2 hwt hgram hPS
  intro w Hd kap hHd hk t0 T hTT B hB
  have hw : ((D.wt w : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hwt w)
  have e : i - 1 + 1 = i := Nat.sub_add_cancel hi1
  have hlev : ∀ h ∈ Hd, TB.level h = i - 1 := fun h hh => (hHd h hh).1
  have hpsd : TB.PSDOn Hd (fun h h' => kap h' h) := hT _ Hd kap ((hA _ Hd kap).1.mpr hk)
  have hT' : ∀ t ∈ T, t ≠ 0 ∧ t - t0 ∈ D.La i 1 := by
    intro t ht
    refine ⟨(hTT t ht).1, ?_⟩
    have h2 := (hTT t ht).2
    change t - t0 ∈ D.La (i - 1 + 1) 1 at h2
    rwa [e] at h2
  have hN : ∀ t, TA.Nst (Φ w) Hd kap 1 t t = D.Nst ε i 1 w Hd (fun h h' => kap h' h) t t := by
    intro t
    unfold TA.Nst TB.Data.Nst
    simp only [hgram]
    rw [Finset.sum_comm, eq_div_iff hw, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [TA.ext, TB.join]
    ring
  refine Eq.trans_le ?_ (hPS ε hε i hi1 hi2 w Hd hlev _ hpsd t0 B hB T hT')
  exact Finset.sum_congr rfl fun t _ => congrArg Complex.re (hN t)

theorem block_poisson_frame : Formalism.FourierDecayAlt.J.BlockPoissonFrame := by
  intro hEmb hTD hTw hPow E _ _ _ g r hg i hi1 hi2
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
  have hdd : S6.dd E ≠ 0 := by
    unfold S6.dd
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    first
      | exact differentIdeal_ne_bot
      | (intro h; have h2 := NumberField.absNorm_differentIdeal (K := E); rw [h, Ideal.absNorm_bot] at h2; exact NumberField.discr_ne_zero E (Int.natAbs_eq_zero.mp h2.symm))
  have hB0 : ∀ ν : ℤ, S6.idl E g 2 ν ≠ 0 := by
    intro ν
    unfold S6.idl
    refine mul_ne_zero (zpow_ne_zero _ hdd) ?_
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact zpow_ne_zero _ hgE
  have hBA : ∀ ν : ℤ, S6.idl E g 2 ν ≤ S6.idl E g 1 ν := by
    intro ν
    unfold S6.idl
    have hs : FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ (2 : ℤ)) ≤
        FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ (1 : ℤ)) := by
      rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_spanSingleton]
      exact ⟨(g : 𝓞 E), by simp only [Algebra.smul_def, map_natCast, zpow_one, zpow_two]⟩
    first
      | exact FractionalIdeal.mul_le.mpr fun a ha b hb => FractionalIdeal.mul_mem_mul ha (hs hb)
      | exact mul_le_mul_left' hs _
      | (gcongr; exact hs)
  have hc0 : S6.rd E ^ (-(S6.nuBlock r i 1)) ≠ 0 := zpow_ne_zero _ (Jx4.rd_pos E).ne'
  obtain ⟨hinj, -, -, hsm, -⟩ := hEmb E
  refine ⟨?_, ?_, ?_, ?_⟩
  · beta_reduce
    have hfun : ⇑(semb E (S6.rd E ^ (-(S6.nuBlock r i 1)))) =
        fun t => S6.rd E ^ (-(S6.nuBlock r i 1)) • cemb E t := funext (hsm _)
    rw [hfun]
    exact (smul_right_injective (CV E) hc0).comp hinj
  · beta_reduce
    intro t ht
    exact Submodule.mem_map.mpr ⟨t, ht, rfl⟩
  · beta_reduce
    unfold dm
    ext w
    simp
  · beta_reduce
    intro μ hμ
    have hL := hTw E _ _ 1 (hB0 (S6.nuBlock r i 1)) (hBA _) (hPow E g 2 (S6.nuBlock r i 1))
    exact (hTD E _ g _ hg hc0 hL.2 μ).1 hμ

theorem lattice_x_eq_lambda_one : Formalism.FourierDecayAlt.J.XIsLamOne := by
  intro m i C ka N I A g B
  have h : 2 * (i - 1) + 1 - 1 = 2 * i - 2 := by omega
  refine ⟨?_, ?_⟩
  · unfold Sz.xThreshold Sz.lamThreshold
    rw [h]
  · unfold Sz.xHat Sz.lamHat
    rw [h]

theorem frame_product_identities : Formalism.FourierDecayAlt.J.FrameProducts := by
  intro r i s C rd g N I A TT hi hs hrd hg
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hrd0 : rd ≠ 0 := hrd.ne'
  have hg0 : g ≠ 0 := hg.ne'
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have e1 : 2 * r + 2 - 1 = 2 * r + 1 := by omega
  constructor
  · have hz : rd ^ (S6.nuBlock (r : ℤ) ((n + 1 : ℕ) : ℤ) ((t + 1 : ℕ) : ℤ) + 1) =
        rd ^ (2 * r + 1) / rd ^ (2 * n + t) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd0]
      congr 1
      unfold S6.nuBlock
      push_cast
      ring
    have e2 : 2 * (n + 1 - 1) + (t + 1) - 1 = 2 * n + t := by omega
    unfold Sz.lamThreshold Sz.lamHat
    rw [hz, e1, e2]
    have b1 : C * (2 * Real.pi / g) * N / I = (2 * Real.pi / g) * (C * N / I) := by ring
    have b2 : C * (2 * Real.pi / rd) * N / (g * I) = (2 * Real.pi / (rd * g)) * (C * N / I) := by ring
    rw [b1, b2, mul_pow, mul_pow]
    generalize C * N / I = X
    simp only [div_eq_mul_inv, mul_pow, inv_pow, mul_inv, inv_inv]
    ring
  · have hz : rd ^ (S6.nuBlock (r : ℤ) ((n + 1 : ℕ) : ℤ) ((r : ℤ) + 2 - ((n + 1 : ℕ) : ℤ))) =
        rd ^ r / rd ^ n := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd0]
      congr 1
      unfold S6.nuBlock
      push_cast
      ring
    have key : ∀ P a : ℝ, 0 ≤ a → √P * a = √(P * a ^ 2) := fun P a ha => by
      rw [Real.sqrt_mul' _ (sq_nonneg a), Real.sqrt_sq ha]
    rw [hz, key _ _ (mul_nonneg hg.le (div_nonneg (pow_nonneg hrd.le _) (pow_nonneg hrd.le _)))]
    unfold Sz.lamPrimeHat Sz.lamPrimeSq
    congr 1
    have e3 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    have e4 : 2 * (n + 1 - 1) = 2 * n := by omega
    have e5 : 2 * (n + 1) - 2 = 2 * n := by omega
    rw [e1, e3, e4, e5]
    have b3 : C * (2 * Real.pi / rd) * N / I = (2 * Real.pi / rd) * (C * N / I) := by ring
    rw [b3, mul_pow]
    generalize C * N / I = X
    generalize (Real.sqrt TT)⁻¹ = Y
    simp only [div_eq_mul_inv, mul_pow, inv_pow, mul_inv, inv_inv]
    have hg1 : g * g⁻¹ = 1 := mul_inv_cancel₀ hg0
    have hr1 : rd * rd⁻¹ = 1 := mul_inv_cancel₀ hrd0
    linear_combination
      (C * A * Y * X ^ (2 * n) * ((2 * Real.pi) ^ (2 * r + 1))⁻¹ * (2 * Real.pi) ^ (2 * n + 1) *
          g ^ (2 * r + 2) * (g ^ (2 * n))⁻¹ * rd ^ (2 * r) * (rd ^ (2 * n))⁻¹) * hg1 -
        (C * A * Y * X ^ (2 * n) * ((2 * Real.pi) ^ (2 * r + 1))⁻¹ * (2 * Real.pi) ^ (2 * n + 1) *
          g ^ (2 * r + 2) * (g ^ (2 * n))⁻¹ * rd ^ (2 * r) * (rd ^ (2 * n))⁻¹) * hr1

end Formalism.FourierDecayAlt.P
