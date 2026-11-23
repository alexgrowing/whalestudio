import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.DiffBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.VolOne
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

open scoped Pointwise

private theorem sub_ct_le_of_altSum {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] (f : CC K n) (φ : L2 μ) {r M : ℕ} (hM : 0 < M) (x : G1 K n) (k : ℕ) {B : ℝ}
    (hB : ∀ y : Fin (k + 1) → UPos n r → 𝔸[K], (∀ i, y i ∈ scaledUnipFD K n r M) →
      ‖altSum (k + 1) (fun s => rc μ f φ (unipOne K n r s * x)) y 0‖ ≤ B) :
    ‖rc μ f φ x - ct r (rc μ f φ) x‖ ≤ B := by
  set H : (UPos n r → 𝔸[K]) → ℂ := fun s => rc μ f φ (unipOne K n r s * x) with hH
  set c : ℂ := ct r (rc μ f φ) x with hc
  have hHc : Continuous H :=
    (continuous_rconv (Gam K n) μ f φ).comp ((continuous_unipOne r).mul continuous_const)
  have hper : ∀ ξ ∈ unipLattice K n r, ∀ s, H (ξ + s) = H s := by
    intro ξ hξ s
    simp only [H, rc]
    rw [unipOne_add, mul_assoc,
      rconv_mul_left (Gam K n) μ f φ (unipOne_mem_rationalGLOne r ⟨ξ, hξ⟩)]
  have hD := isAddFundamentalDomain_scaledUnipFD (K := K) (n := n) (r := r) hM
  have hD1 := unipMeasure_scaledUnipFD (K := K) (n := n) (r := r) hM
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_scaledUnipFD (K := K) (n := n) r hM
  have hint : ∀ t, IntegrableOn (fun y => H (t + y)) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    fun t => ((hHc.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact
      hC).mono_set hDC
  have hcint : IntegrableOn (fun _ : UPos n r → 𝔸[K] => c) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    integrableOn_const (by rw [hD1]; exact ENNReal.one_ne_top)
  have hmean0 : ∫ y in scaledUnipFD K n r M, H y ∂unipMeasure K n r = c := by
    rw [hD.setIntegral_eq isAddFundamentalDomain_unipFundamentalDomain fun ξ s => hper ξ ξ.2 s]
    rfl
  have hi0 : IntegrableOn H (scaledUnipFD K n r M) (unipMeasure K n r) := by simpa using hint 0
  have hmean : ∫ y in scaledUnipFD K n r M, (H y - c) ∂unipMeasure K n r = 0 := by
    rw [integral_sub hi0 hcint, hmean0, setIntegral_const, measureReal_def, hD1]
    simp
  have h0 := norm_le_of_forall_altSum_le hD hD1 (k + 1) (fun s => H s - c)
    (fun ξ hξ s => by simp only [hper ξ hξ s]) (fun t => (hint t).sub hcint) hmean B (fun y hy => by
      have := hB y hy
      rw [altSum_succ] at this ⊢
      simpa only [sub_sub_sub_cancel_right] using this)
  simpa [H, unipOne_zero] using h0

private theorem sub_ct_le_of_altSum_inf {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] (f : CC K n) (φ : L2 μ) {r M : ℕ} (hM : 0 < M) (x : G1 K n)
    (hfin : ∀ z : UPos n r → 𝔸[K], (∀ p, (z p).1 = 0) →
      (∀ p, ∃ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
        (z p).2 = (M : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) * a) →
      ∀ w, f ((x⁻¹ * unipOne K n r z * x)⁻¹ * w) = f w)
    (k : ℕ) {B : ℝ}
    (hB : ∀ y : Fin (k + 1) → UPos n r → 𝔸[K], (∀ i, y i ∈ scaledUnipFD K n r M) →
      ‖altSum (k + 1) (fun s => rc μ f φ (unipOne K n r (truncInf s) * x)) y 0‖ ≤ B) :
    ‖rc μ f φ x - ct r (rc μ f φ) x‖ ≤ B := by
  refine sub_ct_le_of_altSum (r := r) μ f φ hM x k fun y hy => ?_
  have key : ∀ ε : Fin (k + 1) → Bool,
      rc μ f φ (unipOne K n r (0 + altPoint y ε) * x) =
        rc μ f φ (unipOne K n r (truncInf (0 + altPoint y ε)) * x) := by
    intro ε
    rw [zero_add]
    have hfinP := hfin (truncFin (altPoint y ε)) (fun p => rfl) fun p => by
      obtain ⟨a, ha, hPa⟩ := exists_finite_altPoint_eq_natCast_mul hM y hy ε p
      exact ⟨a, ha, hPa⟩
    have hP : unipOne K n r (altPoint y ε) * x = unipOne K n r (truncInf (altPoint y ε)) * x *
        (x⁻¹ * unipOne K n r (truncFin (altPoint y ε)) * x) := by
      simp only [mul_assoc, mul_inv_cancel_left]
      rw [← mul_assoc, ← unipOne_add, truncInf_add_truncFin]
    rw [hP]
    exact rconv_mul_right μ f φ hfinP _
  have heq : altSum (k + 1) (fun s => rc μ f φ (unipOne K n r s * x)) y 0 =
      altSum (k + 1) (fun s => rc μ f φ (unipOne K n r (truncInf s) * x)) y 0 := by
    rw [altSum_eq_sum, altSum_eq_sum]
    exact Finset.sum_congr rfl fun ε _ => congrArg (altSign ε • ·) (key ε)
  rw [heq]
  exact hB y hy

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.rootDecay :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n), IsLeftSmooth a → ∀ (ω : Set (AdelicGLn.AdelicGL K n)) (t : ℝ), Bor ω → 0 < t →
      ∀ (r : ℕ) (hr : 0 < r) (hrn : r < n), ∃ N : ℕ, ∀ k : ℕ, ∃ C : ℝ, ∀ (φ : L2 μ) (ρ : Fin n → ℝ) (x : G1 K n) (R : ℝ), Sg ω ρ x → Full t ρ → 1 ≤ R → Rat R ρ →
        ‖rc μ a φ x - ct r (rc μ a φ) x‖ ≤ C * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩) ^ k * R ^ N * ‖φ‖ := by
  intro K _ _ n μ _ f hf ω t hBor ht r hr hrn
  obtain ⟨hω, hωB⟩ := hBor
  obtain ⟨U, hU, hUf⟩ := hf.2
  obtain ⟨V₀, hV₀c, hV₀⟩ := exists_compact_mem_nhds (1 : normOneGL K n)
  obtain ⟨Cc, N, hCc⟩ := exists_encard_le_siegel hω ht hV₀c
  refine ⟨N, fun k => ?_⟩
  obtain ⟨M, hM, hMconj⟩ := exists_natCast_conj_unipGL_mem U hU hω r
  obtain ⟨C₁, hC₁⟩ := exists_norm_archMat_conj_le hω hωB ht hr hrn
    (isCompact_scaledInfSet (K := K) M)
  set C₁' := max C₁ 0
  set R₁ := C₁' * t⁻¹
  obtain ⟨c, hc⟩ := diffBd f hf (k + 1) R₁
  set c' := max c 0
  have h𝒞 := isCompact_unipBall (K := K) (n := n) (((k + 1 : ℕ) : ℝ) * R₁)
  set Q := archProj K n '' unipBall (K := K) (n := n) (((k + 1 : ℕ) : ℝ) * R₁) *
    tsupport (f : normOneGL K n → ℂ)
  have hQ : IsCompact Q := (h𝒞.image continuous_archProj).mul f.hasCompactSupport
  obtain ⟨s, -, hs⟩ := hQ.elim_nhds_subcover (fun g => (fun y => y * g) '' V₀) fun g _ => by
    have := (Homeomorph.mulRight g).isOpenMap.image_mem_nhds hV₀
    rw [Homeomorph.coe_mulRight] at this
    simpa only [one_mul] using this
  refine ⟨c' * C₁' ^ k * R₁ * √(μ.real Q * (s.card * max Cc 0)), ?_⟩
  rintro φ ρ x R ⟨hρ, b, hb, kk, hkk, hx⟩ hsieg hR1 hR
  obtain ⟨m₀, hmC₀, hm₀⟩ := hCc b hb ρ hρ hsieg kk hkk x hx R hR1 hR
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = s.card * m₀ := ⟨_, rfl⟩
  have hm : ∀ z : normOneGL K n,
      {γ : rationalGLOne K n | γ • z ∈ (fun y => x * y) '' Q}.encard ≤ m := by
    intro z
    have := encard_le_of_subset_mul s hs hm₀ z
    rw [hmdef]
    exact_mod_cast this
  have hmC : (m : ℝ) ≤ s.card * Cc * R ^ N := by
    rw [hmdef, Nat.cast_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hmC₀ (Nat.cast_nonneg _)
  set gain := ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩
  have hgain0 : 0 ≤ gain := div_nonneg (hρ _).le (hρ _).le
  have hgain : gain ≤ t⁻¹ := by
    have h1 := hsieg ⟨r - 1, by omega⟩ ⟨r, hrn⟩ (by simp; omega)
    rw [div_le_iff₀ (hρ _), ← div_eq_inv_mul, le_div_iff₀ ht, mul_comm]
    exact h1
  have hc'0 : 0 ≤ c' := le_max_right _ _
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  have hgR : C₁' * gain ≤ R₁ := mul_le_mul_of_nonneg_left hgain hC₁'0
  have hg0 : 0 ≤ C₁' * gain := mul_nonneg hC₁'0 hgain0
  set b₀ := c' * ((C₁' * gain) ^ k * R₁)
  have hb₀ : 0 ≤ b₀ := mul_nonneg hc'0 (mul_nonneg (pow_nonneg hg0 _) (hg0.trans hgR))
  have hfinal : ‖rc μ f φ x - ct r (rc μ f φ) x‖ ≤ b₀ * √(μ.real Q * m) * ‖φ‖ := by
    refine sub_ct_le_of_altSum_inf (r := r) μ f φ hM x ?_ k ?_
    · intro z hz1 hz2 w
      obtain ⟨u, hu⟩ := hMconj b hb ρ hρ kk hkk z hz1 hz2
      have hxu : x⁻¹ * unipOne K n r z * x = finOne K n (u : AdelicGLn.integralFiniteGL K n) := by
        refine Subtype.ext ?_
        change (x : AdelicGLn.AdelicGL K n)⁻¹ * unipGL z * (x : AdelicGLn.AdelicGL K n) =
          finEmb K n _
        rw [hx]
        exact hu
      rw [hxu, ← map_inv]
      exact hUf _ (U.inv_mem u.2) w
    · intro y hy
      set Y : Fin (k + 1) → ArchMatrix K n :=
        fun i => conjArch K n (x : AdelicGLn.AdelicGL K n) (truncInf (y i))
      have hYY : ∀ i j, Y i * Y j = 0 := fun i j => conjArch_mul_conjArch _ _ _
      have hYn : ∀ i, ‖Y i‖ ≤ C₁' * gain := by
        intro i
        have h1 := hC₁ b hb ρ hρ hsieg kk hkk (truncInf (y i)) (fun p => rfl)
          (fun p => infinite_mem_scaledInfSet hM (hy i) p)
        have h2 : Y i = archMat K n ((((b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) *
            kk)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
            blockEntry (truncInf (y i)) * ((b * diagUnits n (fun i => posIdele (K := K) (ρ i)
              (hρ i)) * kk : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
          simp only [Y, conjArch, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hx]
        rw [h2]
        exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgain0)
      have hYR : ∀ i, ‖Y i‖ ≤ R₁ := fun i => (hYn i).trans hgR
      have hex : ∀ ε : Fin (k + 1) → Bool, ∃ C : ArchUnits K n,
          archProj K n C = x⁻¹ * unipOne K n r (truncInf (altPoint y ε)) * x ∧
            (C : ArchMatrix K n) = 1 + altPoint Y ε := by
        intro ε
        obtain ⟨C, hC1, hC2⟩ := exists_archProj_eq_conj x (truncInf (altPoint y ε)) fun p => rfl
        refine ⟨C, hC1, ?_⟩
        rw [hC2, ← truncInfHom_apply, map_altPoint (truncInfHom n r),
          map_altPoint (conjArch K n (x : AdelicGLn.AdelicGL K n))]
        rfl
      choose Cε hCε1 hCε2 using hex
      have hsum : altSum (k + 1) (fun s => rc μ f φ (unipOne K n r (truncInf s) * x)) y 0 =
          ∑ ε, (altSign ε : ℂ) * rconv (rationalGLOne K n) μ f φ (x * archProj K n (Cε ε)) := by
        rw [altSum_eq_sum]
        refine Finset.sum_congr rfl fun ε _ => ?_
        rw [zero_add, hCε1 ε, zsmul_eq_mul]
        have : x * (x⁻¹ * unipOne K n r (truncInf (altPoint y ε)) * x) =
            unipOne K n r (truncInf (altPoint y ε)) * x := by group
        rw [this]
      rw [hsum]
      have hb' : ∀ w, ‖∑ ε, (altSign ε : ℂ) * f ((archProj K n (Cε ε))⁻¹ * w)‖ ≤ b₀ := by
        intro w
        refine (hc Y hYY hYR Cε hCε2 w).trans ?_
        have hprod : ∏ i, ‖Y i‖ ≤ (C₁' * gain) ^ (k + 1) := by
          rw [← Fin.prod_const]
          exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hYn i
        have hprod' : ∏ i, ‖Y i‖ ≤ (C₁' * gain) ^ k * R₁ := by
          refine hprod.trans ?_
          rw [pow_succ]
          exact mul_le_mul_of_nonneg_left hgR (pow_nonneg hg0 _)
        calc c * ∏ i, ‖Y i‖ ≤ c' * ∏ i, ‖Y i‖ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _)
                (Finset.prod_nonneg fun i _ => norm_nonneg _)
          _ ≤ b₀ := mul_le_mul_of_nonneg_left hprod' hc'0
      have hmem : ∀ ε, Cε ε ∈ unipBall (K := K) (n := n) (((k + 1 : ℕ) : ℝ) * R₁) := fun ε =>
        mem_unipBall_of_val_eq hYY hYR (hCε2 ε)
      have hsq := enorm_sum_altSign_rconv_sq_le μ f φ x h𝒞 Cε hmem hb' hm
      have hA : ENNReal.ofReal b₀ ^ 2 * μ Q * (m : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hQ.measure_lt_top.ne) (by simp)
      have hle := norm_le_of_enorm_sq_le hA (by rw [mul_assoc]; exact hsq)
      refine hle.trans (le_of_eq ?_)
      congr 1
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hb₀,
        ENNReal.toReal_natCast, Real.sqrt_mul (by positivity), Real.sqrt_mul' _ (by positivity),
        Real.sqrt_sq hb₀, measureReal_def, mul_assoc, Real.sqrt_mul ENNReal.toReal_nonneg]
  refine hfinal.trans ?_
  have hμQ : 0 ≤ μ.real Q := measureReal_nonneg
  have hRN : 1 ≤ R ^ N := one_le_pow₀ hR1
  have hm' : (m : ℝ) ≤ s.card * max Cc 0 * R ^ N :=
    hmC.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _)
      (Nat.cast_nonneg _)) (pow_nonneg (by linarith) _))
  have hsqrt : √(μ.real Q * m) ≤ √(μ.real Q * (s.card * max Cc 0)) * √(R ^ N) := by
    rw [← Real.sqrt_mul (mul_nonneg hμQ (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)))]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hm' hμQ
  have hsR : √(R ^ N) ≤ R ^ N := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hsqrt' : √(μ.real Q * m) ≤ √(μ.real Q * (s.card * max Cc 0)) * R ^ N :=
    hsqrt.trans (mul_le_mul_of_nonneg_left hsR (Real.sqrt_nonneg _))
  calc b₀ * √(μ.real Q * m) * ‖φ‖
      ≤ b₀ * (√(μ.real Q * (s.card * max Cc 0)) * R ^ N) * ‖φ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt' hb₀) (norm_nonneg _)
    _ = c' * C₁' ^ k * R₁ * √(μ.real Q * (s.card * max Cc 0)) * gain ^ k * R ^ N * ‖φ‖ := by
        simp only [b₀, mul_pow]
        ring
