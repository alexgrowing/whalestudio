import Formalism.MirabolicMackeyTheory.LocalConditionsWeighted
import Formalism.MirabolicMackeyTheory.MirabolicIsMackey
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LocalConditionsGlobalForm
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem enlarge_initial_lattice : EnlargeInitialLattice := by
  intro K _ _ _ Z _ _ _ _ _ w M Th1 Th hM h1 hT h1T hTM E r h W
  have a := (idxCutLe K Z w ⊤ W M Th hM hT hTM le_top).1
  have b := (idxCutLe K Z w ⊤ W Th Th1 hT h1 h1T le_top).1
  have c := (idxCutLe K Z w ⊤ W Th1 Th1 h1 h1 le_rfl le_top).1
  have d : cut W Th1 ≤ cut W Th := inf_le_inf_right _ h1T
  have e := idxMono K Z w W (cut W M) (cut W Th1) (cut W Th) a c b d
  have e' : (lix w (cut W M) (cut W Th) : ℝ) ≤ (lix w (cut W M) (cut W Th1) : ℝ) := by exact_mod_cast e
  exact le_trans e' (h W)

theorem twist_chain : TwChain := by
  intro K _ _ _ Z _ _ _ _ _ w W e A Th0 ThJ X₃ hA h0 hJ hle ε h
  have a := idxMono K Z w W A _ _ hA h0 hJ (Submodule.map_mono hle)
  have a' : (lix w A (ThJ.map (e.restrictScalars (𝓞 K))) : ℝ) ≤
      (lix w A (Th0.map (e.restrictScalars (𝓞 K))) : ℝ) := by exact_mod_cast a
  linarith

theorem local_conditions_family : OnLocalJ := by
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th ThK Th0 ThJ X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs
    σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 h4 h34 ε hTW d φ hinj hrng Mj Tj hMj hTj
  exact onLocal K Z w P ρ U ψ hMk V₀ e he hr M Th ThK Th0 X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs σ hσ hsc hdata
    a E r ha hE hT0 h0 h3 h4 h34 ε
    (twist_chain K Z w _ e _ Th0 ThJ X₃ (idxCutLe K Z w ⊤ _ M Th hM hTh hle le_top).1 h0 hJ h0J ε hTW)
    d φ hinj hrng Mj Tj hMj hTj

theorem onLocal_of_onLocalJ (h : OnLocalJ) : OnLocal := by
  exact fun K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th ThK Th0 X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs
    σ hσ hsc hdata a E r ha hE hT0 h0 h3 h4 h34 ε hTW =>
    h K Z w P ρ U ψ hMk V₀ e he hr M Th ThK Th0 Th0 X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs
      σ hσ hsc hdata a E r ha hE hT0 h0 h0 le_rfl h3 h4 h34 ε hTW

theorem theta_identity : ThetaIdentity := by
  intro R X Y _ _ _ _ _ θ eX pr e hc hk Mt
  have key : ∀ m, θ (pr (eX m)) = e (θ m) := by
    intro m
    have h1 := hk (eX m) (LinearMap.mem_range_self eX m)
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
    rw [← h1, ← LinearMap.comp_apply θ eX, hc, LinearMap.comp_apply]
  ext y
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨z, ⟨x, ⟨m, hm, rfl⟩, rfl⟩, rfl⟩
    exact ⟨θ m, ⟨m, hm, rfl⟩, (key m).symm⟩
  · rintro ⟨z, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨pr (eX m), ⟨eX m, ⟨m, hm, rfl⟩, rfl⟩, key m⟩

theorem theta_identity_orthogonal : ThetaIdentityOrth := by
  intro R X Y A _ _ _ _ _ _ θ eX p e h hc hsym hp hker hrange
  have hkerθ : ∀ k ∈ LinearMap.ker θ, eX k ∈ LinearMap.ker θ := by
    intro k hk
    rw [LinearMap.mem_ker] at hk ⊢
    rw [← LinearMap.comp_apply θ eX, hc, LinearMap.comp_apply, hk, map_zero]
  have hpp : ∀ x, p (p x) = p x := fun x => by rw [← LinearMap.comp_apply p p, hp]
  have hrp : ∀ x, p x ∈ LinearMap.range p := fun x => LinearMap.mem_range_self p x
  have hsub : ∀ x, x - p x ∈ LinearMap.ker θ := fun x => by
    rw [← hker, LinearMap.mem_ker, map_sub, hpp, sub_self]
  have hEr : ∀ x ∈ LinearMap.range p, eX x ∈ LinearMap.range p := by
    intro x hx
    rw [hrange] at hx ⊢
    intro k hk
    rw [← hsym]
    exact hx _ (hkerθ k hk)
  have hfix : ∀ y ∈ LinearMap.range p, p y = y := by
    rintro y ⟨z, rfl⟩
    exact hpp z
  have hcomm : ∀ x, p (eX x) = eX (p x) := by
    intro x
    have h1 : eX x = eX (p x) + eX (x - p x) := by
      rw [← map_add]
      congr 1
      abel
    have h2 : p (eX (x - p x)) = 0 := by
      rw [← LinearMap.mem_ker, hker]
      exact hkerθ _ (hsub x)
    rw [h1, map_add, h2, add_zero, hfix _ (hEr _ (hrp x))]
  refine ⟨LinearMap.ext hcomm, fun x hx => ⟨?_, hsub x, fun k hk => (hrange (p x)).1 (hrp x) k hk⟩, fun Mt => ?_⟩
  · obtain ⟨y, rfl⟩ := hx
    rw [hcomm]
    exact LinearMap.mem_range_self eX (p y)
  · have key : ∀ m, θ (eX (p m)) = e (θ m) := by
      intro m
      have hm : θ (p m) = θ m := by
        have := hsub m
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
        exact this.symm
      rw [← LinearMap.comp_apply θ eX, hc, LinearMap.comp_apply, hm]
    ext y
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨z, ⟨x, ⟨m, hm, rfl⟩, rfl⟩, rfl⟩
      exact ⟨θ m, ⟨m, hm, rfl⟩, (key m).symm⟩
    · rintro ⟨z, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨eX (p m), ⟨p m, ⟨m, hm, rfl⟩, rfl⟩, key m⟩

theorem trace_class : TraceClass := by
  intro R N Y Γ _ _ _ _ _ _ _ ρ lam θ hθ P
  refine ⟨fun γ' => ?_, ?_, fun N0 hρ hl hP => ?_⟩
  · rw [map_sum, Finset.smul_sum]
    simp only [map_smul]
    apply Fintype.sum_equiv (Equiv.mulLeft γ')
    intro γ
    have hl1 : lam γ'⁻¹ * lam γ' = 1 := by
      first
        | rw [← map_mul, inv_mul_cancel, map_one]
        | rw [← map_mul, mul_left_inv, map_one]
        | simp [← map_mul]
    simp only [Equiv.coe_mulLeft, map_mul, smul_smul]
    rw [← mul_assoc, hl1, one_mul]
    first
      | rfl
      | simp [Module.End.mul_apply]
  · rw [map_sum]
    simp only [map_smul]
    rw [Finset.sum_congr rfl (fun γ _ => (hθ γ P).symm), Finset.sum_const, Finset.card_univ]
    first
      | rw [Nat.cast_smul_eq_nsmul]
      | simp
  · exact AddSubgroup.sum_mem N0 (fun γ _ => hl γ _ (hρ γ P hP))

theorem ceiling_shift : CeilShift := by
  intro ρ vS T ν β hρ
  have hρ' : (ρ : ℝ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hq : (ρ : ℝ) * ((vS : ℝ) / (ρ : ℝ)) = vS := by
    first
      | field_simp
      | exact mul_div_cancel₀ _ hρ'
  have e : (ρ : ℝ) * ((T : ℝ) * (ν - (vS : ℝ) / (ρ : ℝ) + β)) =
      (ρ : ℝ) * ((T : ℝ) * (ν + β)) - (((T : ℤ) * vS : ℤ) : ℝ) := by
    push_cast
    linear_combination (-(T : ℝ)) * hq
  rw [e]
  first
    | rw [Int.ceil_sub_intCast]
    | rw [Int.ceil_sub_int]
    | simp

theorem level_ceiling : LevelCeil := by
  intro ρ T DL Dk g hρ hDL hTD hg
  have hDk : 0 ≤ Dk := le_trans (mul_nonneg (Nat.cast_nonneg T) hDL) hTD
  have hg1 : 0 < g - 1 := by linarith
  have hx : (T : ℝ) * (DL / (g - 1) + 1) ≤ (T : ℝ) + 1 := by
    have e1 : (T : ℝ) * (DL / (g - 1) + 1) = (T : ℝ) * DL / (g - 1) + T := by ring
    have e2 : (T : ℝ) * DL / (g - 1) ≤ 1 := by
      first
        | (rw [div_le_one hg1]; linarith)
        | (rw [div_le_one₀ hg1]; linarith)
        | (rw [div_le_iff₀ hg1]; linarith)
    linarith
  rw [Int.ceil_le]
  push_cast
  exact mul_le_mul_of_nonneg_left hx (by exact_mod_cast hρ)

theorem valuation_pow_alt (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (a : K) (ha : a ≠ 0) (n : ℕ) : vw w (a ^ n) = (n : ℤ) * vw w a := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

private theorem vw_mul_lemma (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) : vw w (a * b) = vw w a + vw w b := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  apply FractionalIdeal.count_mul <;> rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]

theorem scalar_level : ScalarLevel := by
  intro K _ _ _ w nnL nnF q Z1 Z2 T c h1 h2 h3 h4 h5 z1 z2
  rw [vw_mul_lemma K w _ _ (pow_ne_zero _ (mul_ne_zero h1 h4)) (mul_ne_zero (mul_ne_zero h2 (pow_ne_zero _ h3)) h5),
    valuation_pow_alt K w _ (mul_ne_zero h1 h4), vw_mul_lemma K w _ _ h1 h4,
    vw_mul_lemma K w _ _ (mul_ne_zero h2 (pow_ne_zero _ h3)) h5, vw_mul_lemma K w _ _ h2 (pow_ne_zero _ h3),
    valuation_pow_alt K w _ h3, vw_mul_lemma K w _ _ (pow_ne_zero _ h1) h2, valuation_pow_alt K w _ h1, z1, z2]
  ring

private theorem ramw_nonneg_lemma_2 (K : Type) [Field K] [NumberField K] [StarRing K]
    (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ ramw w := by
  unfold ramw vw
  have e : ((plc w : ℕ) : K) = algebraMap (𝓞 K) K ((plc w : ℕ) : 𝓞 K) := by simp
  rw [e, ← FractionalIdeal.coeIdeal_span_singleton]
  apply FractionalIdeal.count_coe_nonneg

theorem level_at_place_alt : LevelPlace := by
  intro K _ _ _ w nnL nnF q Z1 Z2 T c DL Dk g h1 h2 h3 h4 h5 z1 z2 hq hT h0 hTD hg
  rw [scalar_level K w nnL nnF q Z1 Z2 T c h1 h2 h3 h4 h5 z1 z2]
  have hR := ramw_nonneg_lemma_2 K w
  have hc := level_ceiling (ramw w) T DL Dk g hR h0 hTD hg
  have hA : 0 ≤ ramw w * ((T : ℤ) - 1) := mul_nonneg hR (by omega)
  have hB : 0 ≤ (c : ℤ) * vw w q := mul_nonneg (by omega) hq
  linarith

theorem constant_b_bound : ConstB := by
  intro RR PP DF d' n1 nW g' qmin hRR hDF hd hn1 hn hq hqg hPP
  have hg : 0 < g' := lt_of_lt_of_le hq hqg
  have hnW : 0 ≤ nW := le_trans hn1 hn
  have hd3 : 0 ≤ d' ^ 3 := pow_nonneg hd 3
  have hd4 : 0 ≤ d' ^ 4 := pow_nonneg hd 4
  have hPP0 : 0 ≤ PP := by nlinarith [mul_nonneg hd4 hnW]
  have hDF2 : 1 ≤ DF ^ 2 := by nlinarith
  have k1 : 0 ≤ RR * DF ^ 2 * (PP - (d' ^ 4 * nW + 2 * d' ^ 3)) :=
    mul_nonneg (mul_nonneg hRR (sq_nonneg DF)) (by linarith)
  have k2 : 0 ≤ RR * d' ^ 4 * (nW * DF ^ 2 - n1 / 4) :=
    mul_nonneg (mul_nonneg hRR hd4) (by nlinarith)
  have hC : n1 * d' * (RR * d' ^ 3) / 4 + 2 * (RR * d' ^ 3) * DF ^ 2 ≤ RR * PP * DF ^ 2 := by
    nlinarith [k1, k2]
  have hN : 0 ≤ RR * PP * DF ^ 2 := mul_nonneg (mul_nonneg hRR hPP0) (sq_nonneg DF)
  have hinv : g'⁻¹ ≤ qmin⁻¹ := by
    first
      | exact inv_anti₀ hq hqg
      | exact inv_le_inv_of_le hq hqg
      | exact (inv_le_inv hg hq).2 hqg
  calc n1 * d' * (RR * d' ^ 3) / (4 * g') + 2 * (RR * d' ^ 3) * DF ^ 2 / g'
      = (n1 * d' * (RR * d' ^ 3) / 4 + 2 * (RR * d' ^ 3) * DF ^ 2) * g'⁻¹ := by
        first
          | ring
          | (field_simp; ring)
    _ ≤ RR * PP * DF ^ 2 * g'⁻¹ := mul_le_mul_of_nonneg_right hC (inv_nonneg.mpr hg.le)
    _ ≤ RR * PP * DF ^ 2 * qmin⁻¹ := mul_le_mul_of_nonneg_left hinv hN
    _ = RR * PP * DF ^ 2 / qmin := by rw [div_eq_mul_inv]

theorem twist_set_double : TwistSetDouble := by
  intro K _ _ _ J _ ε0 w h
  have hp : 0 ≤ 1 / (plc w : ℝ) ^ 2 := by positivity
  have e2 : (2 : ℝ) / (plc w : ℝ) ^ 2 = 1 / (plc w : ℝ) ^ 2 + 1 / (plc w : ℝ) ^ 2 := by ring
  rw [e2]
  by_cases hc : conjPl w = w
  · simp only [if_pos hc, add_zero] at h
    rw [hc, Finset.sum_add_distrib]
    linarith
  · simp only [if_neg hc] at h
    linarith

theorem local_conditions_global_set : OnExportSet := by
  classical
  intro K _ _ _ D hD Tup μ J _ d hd M T θ S e0 r0 ε0 F0 errl Jx vU0 gq dK EA Rb EJ δq E3 hδ h1 h2 hsh hv
    hdep htw0 hEA hRb hEJ hE3
  have hR : RamBasic := ramBasic
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have htw : ∀ w ∈ S, ∑ j, (ε0 w j + ε0 (conjPl w) j) ≤ 2 / (plc w : ℝ) ^ 2 :=
    fun w hw => twist_set_double K J ε0 w (by convert htw0 w hw)
  obtain ⟨c1, c2, c3⟩ := local_conditions_global_form K D hD Tup μ J d hd M T θ S e0 r0 ε0 F0 errl Jx vU0 gq dK EA Rb EJ δq E3
    hδ h1 h2 hsh hv hdep htw hEA hRb hEJ hE3
  refine ⟨?_, c1, c2, c3⟩
  intro w hw
  obtain ⟨hp, hr1, hpc, hrc, hell⟩ := hR K w
  have hρ : (1 : ℝ) ≤ (ramw w : ℝ) := by exact_mod_cast hr1
  obtain ⟨hv0, hvc, hvg⟩ := hv w hw
  have key : ∀ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
        (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ)) ≤
      (2 * ((ramw w : ℝ) * F0 w j) +
          (ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)))) * D +
        (ramw w : ℝ) * (ε0 w j + ε0 (conjPl w) j) := by
    intro j
    have a1 := h1 w hw j
    have a2 := h2 w hw j
    rw [hrc, hvc] at a2
    have hdj : (d j : ℝ) = D := by exact_mod_cast hd j
    rw [hdj] at a1 a2
    have a3 := hdep w hw j
    have a4 := hsh j
    have e1 : (r0 w j + dK j * vU0 w) / δq = r0 w j / δq + dK j / δq * vU0 w := by
      field_simp
    have e2 : (r0 (conjPl w) j + dK j * vU0 w) / δq = r0 (conjPl w) j / δq + dK j / δq * vU0 w := by
      field_simp
    have e3 : (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)) * D = r0 w j / δq + r0 (conjPl w) j / δq := by
      field_simp
    rw [e1] at a1
    rw [e2] at a2
    have b1 : dK j / δq * vU0 w ≤ 3 * (D : ℝ) * vU0 w := mul_le_mul_of_nonneg_right a4 hv0
    have b2 : (e0 w j + e0 (conjPl w) j + 8 * vU0 w) * (D : ℝ) ≤ (2 * F0 w j + errl w j) * D :=
      mul_le_mul_of_nonneg_right (by linarith) hDr.le
    have b3 : ((e0 w j + vU0 w) * (D : ℝ) + (r0 w j / δq + dK j / δq * vU0 w) + ε0 w j) +
        ((e0 (conjPl w) j + vU0 w) * (D : ℝ) + (r0 (conjPl w) j / δq + dK j / δq * vU0 w) +
          ε0 (conjPl w) j) ≤
        (2 * F0 w j + errl w j) * D + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)) * D +
          (ε0 w j + ε0 (conjPl w) j) := by
      rw [e3]; nlinarith
    have b4 := mul_le_mul_of_nonneg_left b3 (by linarith : (0 : ℝ) ≤ (ramw w : ℝ))
    calc _ ≤ _ := add_le_add a1 a2
      _ = (ramw w : ℝ) * (((e0 w j + vU0 w) * (D : ℝ) + (r0 w j / δq + dK j / δq * vU0 w) + ε0 w j) +
        ((e0 (conjPl w) j + vU0 w) * (D : ℝ) + (r0 (conjPl w) j / δq + dK j / δq * vU0 w) +
          ε0 (conjPl w) j)) := by ring
      _ ≤ _ := b4
      _ = _ := by ring
  calc _ ≤ _ := Finset.sum_le_sum (fun j _ => key j)
    _ = (∑ j, (2 * ((ramw w : ℝ) * F0 w j) +
          (ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ))))) * D +
        (ramw w : ℝ) * ∑ j, (ε0 w j + ε0 (conjPl w) j) := by
          rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ ≤ _ := by
      rw [hell]
      have c1 := mul_le_mul_of_nonneg_left (htw w hw) (by linarith : (0 : ℝ) ≤ (ramw w : ℝ))
      linarith

theorem local_conditions_weighted : LocalConditionsWeighted := by
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th1 Th ThK Th0 ThJ X₃ hM hTh1 hTh hThK h1le hle hFG hEig
    hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 X _ _ _ _ θ' eX pr Mt hc hk h4 h34 ε hTW d φ hinj hrng
    Mj Tj hMj hTj
  have hT0' := enlarge_initial_lattice K Z w M Th1 Th hM hTh1 hTh h1le hle (E : ℝ) r hT0
  have hc' : (θ'.restrictScalars (𝓞 K)) ∘ₗ (eX.restrictScalars (𝓞 K)) =
      (e.restrictScalars (𝓞 K)) ∘ₗ (θ'.restrictScalars (𝓞 K)) :=
    LinearMap.ext fun x => LinearMap.congr_fun hc x
  have hk' : ∀ x ∈ LinearMap.range (eX.restrictScalars (𝓞 K)),
      x - (pr.restrictScalars (𝓞 K)) x ∈ LinearMap.ker (θ'.restrictScalars (𝓞 K)) := by
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
    exact LinearMap.mem_ker.2 (LinearMap.mem_ker.1 (hk _ (LinearMap.mem_range_self eX y)))
  have hid := theta_identity (𝓞 K) X Z (θ'.restrictScalars (𝓞 K)) (eX.restrictScalars (𝓞 K))
    (pr.restrictScalars (𝓞 K)) (e.restrictScalars (𝓞 K)) hc' hk' Mt
  exact local_conditions_family K Z w P ρ U ψ hMk V₀ e he hr M Th ThK Th0 ThJ X₃
    ((Mt.map (θ'.restrictScalars (𝓞 K))).map (e.restrictScalars (𝓞 K))) hM hTh hThK hle hFG hEig hMs hTs
    σ hσ hsc hdata a E r ha hE hT0' h0 hJ h0J h3 h4 h34 ε hTW d φ hinj hrng Mj Tj hMj (hTj.trans hid)

theorem localConditionsFamily_of_weighted (h : LocalConditionsWeighted)
    (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (P : Type) [Group P] [Finite P] (ρ : Representation K P Z)
    (U : Subgroup P) (ψ : P → 𝓞 K) (hMk : IsMackey U ψ)
    (V₀ : Submodule K Z) (e : Z →ₗ[K] Z) (he : e ∘ₗ e = e) (hr : LinearMap.range e = V₀)
    (M Th ThK Th0 ThJ X₃ X₄ : Submodule (𝓞 K) Z)
    (hM : IsLatIn ⊤ M) (hTh : IsLatIn ⊤ Th) (hThK : IsLatIn ⊤ ThK) (hle : Th ≤ M) (hFG : Th0.FG)
    (hEig : Th0 ≤ (eig ρ U ψ).restrictScalars (𝓞 K))
    (hMs : ∀ g : P, M.map ((ρ g).restrictScalars (𝓞 K)) ≤ M)
    (hTs : ∀ g : P, Th.map ((ρ g).restrictScalars (𝓞 K)) ≤ Th)
    (σ : K) (hσ : σ ≠ 0) (hsc : Th ≤ sc σ ThK)
    (hdata : sc ((Nat.card U : ℕ) : K) (cut (eig ρ U ψ) ThK) ≤ Th0)
    (a : K) (E : ℕ) (r : ℝ) (ha : a ≠ 0) (hE : vw w a = (E : ℤ))
    (hT0 : ∀ W : Submodule K Z, (lix w (cut W M) (cut W Th) : ℝ) ≤ (E : ℝ) * (finrank K W : ℝ) + r)
    (h0 : IsLatIn (eig ρ U ψ ⊓ V₀) (Th0.map (e.restrictScalars (𝓞 K))))
    (hJ : IsLatIn (eig ρ U ψ ⊓ V₀) (ThJ.map (e.restrictScalars (𝓞 K)))) (h0J : Th0 ≤ ThJ)
    (h3 : IsLatIn (eig ρ U ψ ⊓ V₀) X₃) (h4 : IsLatIn (eig ρ U ψ ⊓ V₀) X₄) (h34 : X₃ ≤ X₄)
    (ε : ℝ)
    (hTW : (lix w (cut (eig ρ U ψ ⊓ V₀) M) X₃ : ℝ) ≤
      (lix w (cut (eig ρ U ψ ⊓ V₀) M) (ThJ.map (e.restrictScalars (𝓞 K))) : ℝ) + ε)
    (d : ℕ) (φ : (Fin d → K) →ₗ[K] Z) (hinj : Function.Injective φ)
    (hrng : LinearMap.range φ = eig ρ U ψ ⊓ V₀)
    (Mj Tj : Submodule (𝓞 K) (Fin d → K))
    (hMj : Mj.map (φ.restrictScalars (𝓞 K)) = cut (eig ρ U ψ ⊓ V₀) M)
    (hTj : Tj.map (φ.restrictScalars (𝓞 K)) = X₄) :
      (idx w Mj Tj : ℝ) ≤
        ((E : ℝ) - (vw w σ : ℝ) + (vw w ((Nat.card U : ℕ) : K) : ℝ)) * (d : ℝ) +
          (r + (finrank K Z : ℝ) * (vw w ((Nat.card U : ℕ) : K) : ℝ)) / (U.index : ℝ) + ε := by
  have hfix : X₄.map (e.restrictScalars (𝓞 K)) = X₄ := by
    have h4c := h4
    obtain ⟨-, h4s⟩ := h4c
    have hsub : ∀ x ∈ X₄, e x = x := by
      intro x hx
      have hx1 : x ∈ Submodule.span K (X₄ : Set Z) := Submodule.subset_span hx
      rw [h4s] at hx1
      have hx2 : x ∈ LinearMap.range e := by
        rw [hr]
        exact (Submodule.mem_inf.1 hx1).2
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx2
      rw [← LinearMap.comp_apply e e, he]
    ext x
    simp only [Submodule.mem_map, LinearMap.coe_restrictScalars]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hsub y hy]
      exact hy
    · intro hx
      exact ⟨x, hx, hsub x hx⟩
  have hid : X₄.map ((LinearMap.id : Z →ₗ[K] Z).restrictScalars (𝓞 K)) = X₄ := by
    ext x
    simp
  exact h K Z w P ρ U ψ hMk V₀ e he hr M Th Th ThK Th0 ThJ X₃ hM hTh hTh hThK le_rfl hle hFG hEig hMs hTs
    σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 Z LinearMap.id e LinearMap.id X₄
    (by rw [LinearMap.id_comp, LinearMap.comp_id]) (fun x _ => by simp)
    (by rw [hid, hfix]; exact h4) (by rw [hid, hfix]; exact h34) ε hTW d φ hinj hrng Mj Tj hMj
    (by rw [hTj, hfix, hid, hid])

theorem block_type : BlockType := by
  intro R _ I r t A A' B B' C C' D D' hM hB
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hM
  obtain ⟨hTL, hTR, -, -⟩ := hM
  have hB0 : B.map (Ideal.Quotient.mk I) = 0 := by
    ext i j
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hB i j)
  have hTL' : A.map (Ideal.Quotient.mk I) * A'.map (Ideal.Quotient.mk I) = 1 := by
    have h1 := congrArg (fun X => X.map (Ideal.Quotient.mk I)) hTL
    simp only [Matrix.map_add _ (map_add (Ideal.Quotient.mk I)), Matrix.map_mul, hB0, Matrix.zero_mul, add_zero,
      Matrix.map_one _ (map_zero (Ideal.Quotient.mk I)) (map_one (Ideal.Quotient.mk I))] at h1
    exact h1
  have hTR' : A.map (Ideal.Quotient.mk I) * B'.map (Ideal.Quotient.mk I) = 0 := by
    have h1 := congrArg (fun X => X.map (Ideal.Quotient.mk I)) hTR
    simp only [Matrix.map_add _ (map_add (Ideal.Quotient.mk I)), Matrix.map_mul, hB0, Matrix.zero_mul, add_zero,
      Matrix.map_zero _ (map_zero (Ideal.Quotient.mk I))] at h1
    exact h1
  have hA'A : A'.map (Ideal.Quotient.mk I) * A.map (Ideal.Quotient.mk I) = 1 := by
    first
      | exact mul_eq_one_comm.1 hTL'
      | exact Matrix.mul_eq_one_comm.mp hTL'
      | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hTL'
  have hB'0 : B'.map (Ideal.Quotient.mk I) = 0 := by
    calc B'.map (Ideal.Quotient.mk I)
        = (A'.map (Ideal.Quotient.mk I) * A.map (Ideal.Quotient.mk I)) * B'.map (Ideal.Quotient.mk I) := by
          rw [hA'A, Matrix.one_mul]
      _ = A'.map (Ideal.Quotient.mk I) * (A.map (Ideal.Quotient.mk I) * B'.map (Ideal.Quotient.mk I)) :=
          Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hTR', Matrix.mul_zero]
  have hent : ∀ {m n : Type} (X : Matrix m n R), X.map (Ideal.Quotient.mk I) = 0 → ∀ i j, X i j ∈ I := by
    intro m n X hX i j
    exact Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun hX i) j)
  refine ⟨?_, hent _ ?_, hent _ ?_, hent _ hB'0⟩
  · rw [← Ideal.Quotient.eq]
    simp only [RingHom.map_det, map_mul, RingHom.mapMatrix_apply, Matrix.fromBlocks_map, hB0,
      Matrix.det_fromBlocks_zero₁₂]
  · rw [Matrix.map_sub _ (map_sub (Ideal.Quotient.mk I)), Matrix.map_mul,
      Matrix.map_one _ (map_zero (Ideal.Quotient.mk I)) (map_one (Ideal.Quotient.mk I)), hTL', sub_self]
  · rw [Matrix.map_sub _ (map_sub (Ideal.Quotient.mk I)), Matrix.map_mul,
      Matrix.map_one _ (map_zero (Ideal.Quotient.mk I)) (map_one (Ideal.Quotient.mk I)), hA'A, sub_self]

theorem gapConditions_of_largeGaps : GapNum := by
  intro T D nW r t h0 c hD hr ht hnW hT
  have h2 : 2 * (D + 2) ≤ (D + 2) * nW := by nlinarith
  have hb : 0 ≤ T + D + 2 + r := by linarith
  have hle : T + D + 2 + r ≤ 3 / 2 * T := by linarith
  have hsq := mul_self_le_mul_self hb hle
  have key : (T + D + 2) * (T + D + 2 + 2 * r) ≤ 9 / 4 * T ^ 2 := by nlinarith [sq_nonneg r]
  have e : (3.75 : ℝ) = 15 / 4 := by norm_num
  rw [e]
  exact ⟨by nlinarith [sq_nonneg T], fun hh hc => by nlinarith [sq_nonneg T]⟩

theorem primitive_line : PrimitiveLine := by
  intro R K σ _ _ _ hinj Del Q m c hD hc
  have hcoef : c = algebraMap R K (Q.coeff m) := by
    have h1 := congrArg (MvPolynomial.coeff m) hc
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.coeff_map, hD, map_one, smul_eq_mul,
      mul_one] at h1
    exact h1
  refine ⟨Q.coeff m, hcoef.symm, ?_⟩
  have hmap : MvPolynomial.map (algebraMap R K) Q = MvPolynomial.map (algebraMap R K) (Q.coeff m • Del) := by
    rw [← hc, hcoef, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
  first
    | exact MvPolynomial.map_injective _ hinj hmap
    | exact MvPolynomial.map_injective hinj hmap

example : ⌈((1 : ℤ) : ℝ) * (((3 : ℕ) : ℝ) * ((2 : ℝ) / (15 - 1) + 1))⌉ = (1 : ℤ) * (((3 : ℕ) : ℤ) + 1) := by
  rw [Int.ceil_eq_iff]; constructor <;> norm_num

example : ¬ (⌈((1 : ℤ) : ℝ) * (((3 : ℕ) : ℝ) * ((2 : ℝ) / (2 - 1) + 1))⌉ ≤ (1 : ℤ) * (((3 : ℕ) : ℤ) + 1)) := by
  rw [Int.ceil_le]; norm_num

example : (1 : ℝ) * 1 * (1 * 1 ^ 3) / (4 * 1) + 2 * (1 * 1 ^ 3) * 1 ^ 2 / 1 ≤ 1 * 3 * 1 ^ 2 / 1 :=
  constant_b_bound 1 3 1 1 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example (Mt : Submodule ℤ (ℤ × ℤ)) :
    ((Mt.map (LinearMap.id : ℤ × ℤ →ₗ[ℤ] ℤ × ℤ)).map
      ((LinearMap.inl ℤ ℤ ℤ) ∘ₗ (LinearMap.fst ℤ ℤ ℤ))).map (LinearMap.fst ℤ ℤ ℤ) =
      (Mt.map (LinearMap.fst ℤ ℤ ℤ)).map (LinearMap.id : ℤ →ₗ[ℤ] ℤ) :=
  theta_identity ℤ (ℤ × ℤ) ℤ (LinearMap.fst ℤ ℤ ℤ) LinearMap.id _ LinearMap.id rfl
    (by intro x _; simp [LinearMap.mem_ker]) Mt

example : (LinearMap.inl ℤ ℤ ℤ ∘ₗ LinearMap.fst ℤ ℤ ℤ) ∘ₗ (LinearMap.id : ℤ × ℤ →ₗ[ℤ] ℤ × ℤ) =
    (LinearMap.id : ℤ × ℤ →ₗ[ℤ] ℤ × ℤ) ∘ₗ (LinearMap.inl ℤ ℤ ℤ ∘ₗ LinearMap.fst ℤ ℤ ℤ) :=
  (theta_identity_orthogonal ℤ (ℤ × ℤ) ℤ ℤ (LinearMap.fst ℤ ℤ ℤ) LinearMap.id
    (LinearMap.inl ℤ ℤ ℤ ∘ₗ LinearMap.fst ℤ ℤ ℤ) LinearMap.id (fun x y => x.1 * y.1 + x.2 * y.2) rfl
    (fun _ _ => rfl) (by ext <;> simp)
    (by ext x; simp [LinearMap.mem_ker])
    (by
      intro x
      constructor
      · rintro ⟨y, rfl⟩ k hk
        have : k.1 = 0 := by simpa [LinearMap.mem_ker] using hk
        simp [this]
      · intro hx
        have := hx (0, 1) (by simp [LinearMap.mem_ker])
        refine ⟨x, ?_⟩
        ext <;> simp at this ⊢
        exact this.symm)).1

example : ((8 : ℝ) + 0 + 2) * (8 + 0 + 2 + 2 * 2) ≤ 3.75 * 8 ^ 2 :=
  (gapConditions_of_largeGaps 8 0 2 2 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1

theorem onExport_of_onExportSet (h : OnExportSet) : OnExport := by
  intro K _ _ _ D hD Tup μ J _ d hd M T θ S e0 r0 ε0 F0 errl Jx vU0 gq dK EA Rb EJ δq E3 hδ h1 h2 h3 h4 h5 h6 h7 h8
    h9 h10
  obtain ⟨-, hA, hB, hC⟩ := h K D hD Tup μ J d hd M T θ S e0 r0 ε0 F0 errl Jx vU0 gq dK EA Rb EJ δq E3 hδ h1 h2 h3
    h4 h5 (fun w hw => by
    have hw6 := h6 w hw
    have hp : 0 ≤ 1 / (plc w : ℝ) ^ 2 := by positivity
    by_cases hc : conjPl w = w
    · simp only [if_pos hc, add_zero]
      rw [hc, Finset.sum_add_distrib] at hw6
      by_cases hs : 0 ≤ ∑ j, ε0 w j
      · linarith
      · push_neg at hs
        linarith
    · simp only [if_neg hc]
      exact hw6) h7 h8 h9 h10
  exact ⟨hA, hB, hC⟩

open Classical in

theorem twistSetDouble_finset (K : Type) [Field K] [NumberField K] [StarRing K] (J : Type) [Fintype J]
    (ε0 : HeightOneSpectrum (𝓞 K) → J → ℝ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (h : ∀ w ∈ S, ∑ j, (ε0 w j + (if conjPl w = w then 0 else ε0 (conjPl w) j)) ≤ 1 / (plc w : ℝ) ^ 2) :
    ∀ w ∈ S, ∑ j, (ε0 w j + ε0 (conjPl w) j) ≤ 2 / (plc w : ℝ) ^ 2 := by
  intro w hw
  exact twist_set_double K J ε0 w (h w hw)

theorem levelCeil_tower (ρ1 ρ2 : ℤ) (T : ℕ) (DL Dk g : ℝ) (h1 : 0 ≤ ρ1) (h2 : 0 ≤ ρ2) (h3 : 0 ≤ DL)
    (h4 : (T : ℝ) * DL ≤ Dk) (h5 : 2 * Dk + 2 < g) :
    ρ1 * ⌈(ρ2 : ℝ) * ((T : ℝ) * (DL / (g - 1) + 1))⌉ ≤ (ρ1 * ρ2) * ((T : ℤ) + 1) := by
  calc ρ1 * ⌈(ρ2 : ℝ) * ((T : ℝ) * (DL / (g - 1) + 1))⌉ ≤ ρ1 * (ρ2 * ((T : ℤ) + 1)) :=
        mul_le_mul_of_nonneg_left (level_ceiling ρ2 T DL Dk g h2 h3 h4 h5) h1
    _ = (ρ1 * ρ2) * ((T : ℤ) + 1) := by ring

example : ⌈((2 : ℤ) : ℝ) * (1.25 : ℝ)⌉ < 2 * ⌈((1 : ℤ) : ℝ) * (1.25 : ℝ)⌉ := by
  have a : ⌈((2 : ℤ) : ℝ) * (1.25 : ℝ)⌉ = 3 := by rw [Int.ceil_eq_iff]; norm_num
  have b : ⌈((1 : ℤ) : ℝ) * (1.25 : ℝ)⌉ = 2 := by rw [Int.ceil_eq_iff]; norm_num
  rw [a, b]; norm_num

theorem levelPlace_any (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (nnL nnF q Z1 Z2 : K) (T c : ℕ) (E : ℤ) (h1 : nnL ≠ 0) (h2 : nnF ≠ 0) (h3 : q ≠ 0) (h4 : Z1 ≠ 0) (h5 : Z2 ≠ 0)
    (z1 : vw w Z1 = 0) (z2 : vw w Z2 = 0) (hq : 0 ≤ vw w q) (hT : 1 ≤ T) (hE : E ≤ ramw w * ((T : ℤ) + 1)) :
    E - vw w ((nnL * Z1) ^ T * (nnF * q ^ c * Z2)) ≤ ramw w * (2 * (T : ℤ)) - vw w (nnL ^ T * nnF) := by
  rw [scalar_level K w nnL nnF q Z1 Z2 T c h1 h2 h3 h4 h5 z1 z2]
  have hR := ramw_nonneg_lemma_2 K w
  have hA : 0 ≤ ramw w * ((T : ℤ) - 1) := mul_nonneg hR (by omega)
  have hB : 0 ≤ (c : ℤ) * vw w q := mul_nonneg (by omega) hq
  linarith

theorem levelPlace_tower (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (nnL nnF q Z1 Z2 : K) (T c : ℕ) (DL Dk g : ℝ) (ρ1 ρ2 : ℤ) (h1 : nnL ≠ 0) (h2 : nnF ≠ 0) (h3 : q ≠ 0)
    (h4 : Z1 ≠ 0) (h5 : Z2 ≠ 0) (z1 : vw w Z1 = 0) (z2 : vw w Z2 = 0) (hq : 0 ≤ vw w q) (hT : 1 ≤ T) (h0 : 0 ≤ DL)
    (hTD : (T : ℝ) * DL ≤ Dk) (hg : 2 * Dk + 2 < g) (r1 : 0 ≤ ρ1) (r2 : 0 ≤ ρ2) (hρ : ramw w = ρ1 * ρ2) :
    ρ1 * ⌈(ρ2 : ℝ) * ((T : ℝ) * (DL / (g - 1) + 1))⌉ - vw w ((nnL * Z1) ^ T * (nnF * q ^ c * Z2)) ≤
      ramw w * (2 * (T : ℤ)) - vw w (nnL ^ T * nnF) := by
  exact levelPlace_any K w nnL nnF q Z1 Z2 T c _ h1 h2 h3 h4 h5 z1 z2 hq hT
    (by rw [hρ]; exact levelCeil_tower ρ1 ρ2 T DL Dk g r1 r2 h0 hTD hg)

section Instance

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def unitLat : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {(1 : K)}

theorem unitLat_isLatIn : IsLatIn (⊤ : Submodule K K) (unitLat K) := by
  unfold IsLatIn unitLat
  refine ⟨Submodule.fg_span_singleton _, ?_⟩
  first
    | (rw [Submodule.span_span_of_tower]
       exact eq_top_iff.2 fun x _ => Submodule.mem_span_singleton.2 ⟨x, by simp⟩)
    | (refine eq_top_iff.2 fun x _ => ?_
       have h1 : (1 : K) ∈ (Submodule.span (𝓞 K) {(1 : K)} : Set K) := Submodule.subset_span rfl
       have h2 := Submodule.smul_mem (Submodule.span K (Submodule.span (𝓞 K) {(1 : K)} : Set K)) x
         (Submodule.subset_span h1)
       simpa using h2)

theorem eig_trivial : eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) = ⊤ := by
  apply eq_top_iff.2
  intro x _
  unfold eig
  rw [Submodule.mem_iInf]
  intro u
  rw [LinearMap.mem_ker]
  simp

theorem map_id_restrict (A : Submodule (𝓞 K) K) :
    A.map ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K)) = A := by
  first
    | (ext x; simp)
    | exact Submodule.map_id A

theorem localConditionsWeighted_trivial_instance (w : HeightOneSpectrum (𝓞 K)) :
    ∀ (d : ℕ) (φ : (Fin d → K) →ₗ[K] K), Function.Injective φ →
    LinearMap.range φ = eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤ →
    ∀ (Mj Tj : Submodule (𝓞 K) (Fin d → K)),
    Mj.map (φ.restrictScalars (𝓞 K)) =
      cut (eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤) (unitLat K) →
    Tj.map (φ.restrictScalars (𝓞 K)) =
      (((unitLat K).map ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K))).map
        ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K))).map ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K)) →
      (idx w Mj Tj : ℝ) ≤
        (((0 : ℕ) : ℝ) - (vw w (1 : K) : ℝ) + (vw w ((Nat.card (⊤ : Subgroup Unit) : ℕ) : K) : ℝ)) * (d : ℝ) +
          (0 + (finrank K K : ℝ) * (vw w ((Nat.card (⊤ : Subgroup Unit) : ℕ) : K) : ℝ)) /
            ((⊤ : Subgroup Unit).index : ℝ) + 0 := by
  intro d φ hinj hrng Mj Tj hMj hTj
  have hv1 : vw w (1 : K) = 0 := by
    unfold vw
    rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
  have hc : ((Nat.card (⊤ : Subgroup Unit) : ℕ) : K) = 1 := by
    first
      | simp
      | (rw [Subgroup.card_top, Nat.card_unique, Nat.cast_one])
  have hidx : (((⊤ : Subgroup Unit).index : ℕ) : ℝ) = 1 := by
    rw [Subgroup.index_top, Nat.cast_one]
  have hcut : cut (eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤) (unitLat K) = unitLat K := by
    unfold cut
    rw [eig_trivial K]
    simp
  have hMT : Mj = Tj := by
    apply Submodule.map_injective_of_injective (f := φ.restrictScalars (𝓞 K)) hinj
    rw [hMj, hTj, hcut, map_id_restrict K, map_id_restrict K, map_id_restrict K]
  subst hMT
  have h0 : idx w Mj Mj = 0 := by
    unfold idx Formalism.HermitianLatticesTheory.lidx
    exact sub_self _
  rw [h0, hc, hv1, hidx]
  simp

theorem localConditionsWeighted_trivial_coords (w : HeightOneSpectrum (𝓞 K)) :
    ∃ (φ : (Fin 1 → K) →ₗ[K] K) (Mj : Submodule (𝓞 K) (Fin 1 → K)), Function.Injective φ ∧
      LinearMap.range φ = eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤ ∧
      Mj.map (φ.restrictScalars (𝓞 K)) =
        cut (eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤) (unitLat K) ∧
      Mj.map (φ.restrictScalars (𝓞 K)) =
        (((unitLat K).map ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K))).map
          ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K))).map
            ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K)) ∧
      (idx w Mj Mj : ℝ) ≤ 0 := by
  have hcut : cut (eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤) (unitLat K) = unitLat K := by
    unfold cut
    rw [eig_trivial K]
    simp
  refine ⟨(LinearEquiv.funUnique (Fin 1) K K).toLinearMap,
    (unitLat K).comap ((LinearEquiv.funUnique (Fin 1) K K).toLinearMap.restrictScalars (𝓞 K)),
    (LinearEquiv.funUnique (Fin 1) K K).injective, ?_, ?_, ?_, ?_⟩
  · rw [eig_trivial K, inf_top_eq]
    exact LinearEquiv.range _
  · rw [Submodule.map_comap_eq_of_surjective
      (f := (LinearEquiv.funUnique (Fin 1) K K).toLinearMap.restrictScalars (𝓞 K))
      (LinearEquiv.funUnique (Fin 1) K K).surjective, hcut]
  · rw [Submodule.map_comap_eq_of_surjective
      (f := (LinearEquiv.funUnique (Fin 1) K K).toLinearMap.restrictScalars (𝓞 K))
      (LinearEquiv.funUnique (Fin 1) K K).surjective, map_id_restrict K,
      map_id_restrict K, map_id_restrict K]
  · unfold idx Formalism.HermitianLatticesTheory.lidx
    simp

end Instance

end Formalism.EigenvalueLevelCeiling
