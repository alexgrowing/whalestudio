import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInnerApprox
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsKFinDRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CasselmanWallachExtensionBanachTargetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAveragedOperatorMappingToKFiniteStatement

noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology ENNReal

namespace GlobalTheory.TypeSum.CoefLow

theorem taylor_two {φ φ' φ'' : ℝ → ℂ} (h1 : ∀ t, HasDerivAt φ (φ' t) t) (h2 : ∀ t, HasDerivAt φ' (φ'' t) t) {K : ℝ}
    (hK : ∀ s, |s| ≤ 1 → ‖φ'' s‖ ≤ K) {t : ℝ} (ht : |t| ≤ 1) : ‖φ t - φ 0 - t • φ' 0‖ ≤ K * t ^ 2 := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (by simp))
  have hc : Convex ℝ (Set.Icc (-|t|) |t|) := convex_Icc _ _
  have h0 : (0 : ℝ) ∈ Set.Icc (-|t|) |t| := ⟨by simp, abs_nonneg _⟩
  have a1 : ∀ s ∈ Set.Icc (-|t|) |t|, ‖φ' s - φ' 0‖ ≤ K * |t| := fun s hs => by
    have := hc.norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ') (f' := φ'') (C := K)
      (fun x _ => (h2 x).hasDerivWithinAt) (fun x hx => hK x ((abs_le.2 hx).trans ht)) h0 hs
    rw [sub_zero, Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_left (abs_le.2 hs) hK0)
  have := hc.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun s => φ s - s • φ' 0) (f' := fun s => φ' s - φ' 0)
    (C := K * |t|) (fun x _ => by
      have := (h1 x).fun_sub ((hasDerivAt_id x).smul_const (φ' 0))
      simpa using this.hasDerivWithinAt) a1 h0 (show t ∈ _ from ⟨neg_abs_le t, le_abs_self t⟩)
  rw [sub_zero, Real.norm_eq_abs, mul_assoc, abs_mul_abs_self, zero_smul, sub_zero] at this
  rw [sq, sub_right_comm]
  exact this

theorem hasDerivAt_of_sq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → E} {F' : E} {K : ℝ}
    (h : ∀ t, |t| ≤ 1 → ‖F t - F 0 - t • F'‖ ≤ K * t ^ 2) : HasDerivAt F F' 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add]
  have h1 : (fun t => F t - F 0 - t • F') =O[𝓝 0] fun t : ℝ => t ^ 2 := by
    refine Asymptotics.IsBigO.of_bound K ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with t ht
    rw [Real.norm_eq_abs, abs_sq]
    exact h t (by simpa using ht)
  exact h1.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))

abbrev Bd (I : Type) : Type := lp (fun _ : I => ℂ) ∞

def mkBd {I : Type} (f : I → ℂ) (h : ∃ C, ∀ i, ‖f i‖ ≤ C) : Bd I :=
  ⟨f, memℓp_infty (by obtain ⟨C, hC⟩ := h; exact ⟨C, by rintro _ ⟨i, rfl⟩; exact hC i⟩)⟩

@[simp] theorem mkBd_apply {I : Type} (f : I → ℂ) (h : ∃ C, ∀ i, ‖f i‖ ≤ C) (i : I) : mkBd f h i = f i := rfl

theorem apply_le {I : Type} (F : Bd I) (i : I) : ‖F i‖ ≤ ‖F‖ := lp.norm_apply_le_norm (by simp) F i

theorem wcomp_le {I : Type} {c : I → ℂ} {B : ℝ} (hB : ∀ i, ‖c i‖ ≤ B) (φ : I → I) (F : Bd I) (i : I) :
    ‖c i * F (φ i)‖ ≤ B * ‖F‖ := by
  rw [norm_mul]
  exact mul_le_mul (hB i) (apply_le F _) (norm_nonneg _) ((norm_nonneg _).trans (hB i))

def wcomp {I : Type} (c : I → ℂ) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ i, ‖c i‖ ≤ B) (φ : I → I) : Bd I →L[ℂ] Bd I :=
  LinearMap.mkContinuous
    { toFun := fun F => mkBd (fun i => c i * F (φ i)) ⟨_, wcomp_le hB φ F⟩
      map_add' := fun F G => by ext i; simp [mul_add]
      map_smul' := fun a F => by ext i; simp; ring } B
    fun F => lp.norm_le_of_forall_le (by positivity) (wcomp_le hB φ F)

theorem wcomp_apply {I : Type} (c : I → ℂ) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ i, ‖c i‖ ≤ B) (φ : I → I) (F : Bd I) (i : I) :
    wcomp c B hB0 hB φ F i = c i * F (φ i) := rfl

theorem norm_wcomp {I : Type} (c : I → ℂ) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ i, ‖c i‖ ≤ B) (φ : I → I) :
    ‖wcomp c B hB0 hB φ‖ ≤ B := LinearMap.mkContinuous_norm_le _ hB0 _

variable {n : ℕ} {ε : Fin n → Bool}

def wt (N : ℕ) (g : Mx n) : ℝ := (1 + hs g) ^ N

theorem wt_pos (N : ℕ) (g : Mx n) : 0 < wt N g := pow_pos (by linarith [hs_nonneg g]) _

theorem wt_ne (N : ℕ) (g : Mx n) : (wt N g : ℂ) ≠ 0 := by exact_mod_cast (wt_pos N g).ne'

theorem wt_mul_le (N : ℕ) (g h : Mx n) : wt N (g * h) ≤ wt N g * wt N h := by
  unfold wt
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by linarith [hs_nonneg (g * h)]) (one_add_hs_mul_le g h) N

theorem continuous_wt (N : ℕ) : Continuous (wt N : Mx n → ℝ) := (continuous_const.add continuous_hs).pow N

theorem norm_wt (N : ℕ) (g : Mx n) : ‖(wt N g : ℂ)‖ = wt N g := by
  rw [Complex.norm_real, Real.norm_of_nonneg (wt_pos N g).le]

open Classical in

def rt (ε : Fin n → Bool) (Λ : Type) (N : ℕ) (h : Mx n) : Bd (Λ × UJset ε) →L[ℂ] Bd (Λ × UJset ε) :=
  if hh : h ∈ UJset ε then
    wcomp (fun i => (wt N (i.2.1 * h) : ℂ) / wt N i.2.1) (wt N h) (wt_pos N h).le
      (fun i => by
        rw [norm_div, norm_wt, norm_wt, div_le_iff₀' (wt_pos _ _)]
        exact wt_mul_le _ _ _) fun i => (i.1, ⟨i.2.1 * h, mul_mem_UJ i.2.2 hh⟩)
  else 0

theorem rt_apply {Λ : Type} {N : ℕ} {h : Mx n} (hh : h ∈ UJset ε) (F : Bd (Λ × UJset ε)) (i : Λ × UJset ε) :
    rt ε Λ N h F i = (wt N (i.2.1 * h) : ℂ) / wt N i.2.1 * F (i.1, ⟨i.2.1 * h, mul_mem_UJ i.2.2 hh⟩) := by
  rw [rt, dif_pos hh, wcomp_apply]

theorem modRep_rt (ε : Fin n → Bool) (Λ : Type) (N : ℕ) : ModRep ε (rt ε Λ N) := by
  refine ⟨?_, fun a ha b hb => ?_, 1, N, fun g hg => ?_⟩
  · ext F i
    rw [rt_apply (one_mem_UJ ε)]
    simp [div_self (wt_ne _ _)]
  · ext F i
    rw [ContinuousLinearMap.comp_apply, rt_apply (mul_mem_UJ ha hb), rt_apply ha, rt_apply hb]
    simp only [mul_assoc]
    have := wt_ne N (i.2.1 * a)
    field_simp
  · rw [rt, dif_pos hg, one_mul]
    exact norm_wcomp _ _ _ _ _

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx n → (H →L[ℂ] H)}

theorem sob_smul (c : ℂ) {ℓ : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) : Sobolev₂ (lieSet ε) σ (c • ℓ) := by
  obtain ⟨S, C, hS, hC⟩ := h
  refine ⟨S, ‖c‖ * C, hS, fun w hw => ?_⟩
  rw [LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC w hw) (norm_nonneg _)

theorem sob_sub {ℓ ℓ' : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) (h' : Sobolev₂ (lieSet ε) σ ℓ') :
    Sobolev₂ (lieSet ε) σ (ℓ - ℓ') := by
  obtain ⟨S, C, hS, hC⟩ := h
  obtain ⟨S', C', hS', hC'⟩ := h'
  refine ⟨S ++ S', |C| + |C'|, words_append hS hS', fun w hw => ?_⟩
  change _ ≤ _ * sobNorm σ (S ++ S') w
  have e1 : ‖ℓ w‖ ≤ C * sobNorm σ S w := hC w hw
  have e2 : ‖ℓ' w‖ ≤ C' * sobNorm σ S' w := hC' w hw
  rw [LinearMap.sub_apply, sobNorm_append]
  have := norm_sub_le (ℓ w) (ℓ' w)
  have a := sobNorm_nonneg σ S w
  have b := sobNorm_nonneg σ S' w
  nlinarith [le_abs_self C, le_abs_self C', abs_nonneg C, abs_nonneg C', mul_nonneg (abs_nonneg C) b,
    mul_nonneg (abs_nonneg C') a, mul_le_mul_of_nonneg_right (le_abs_self C) a,
    mul_le_mul_of_nonneg_right (le_abs_self C') b]

def Forms (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) (a : H) (N : ℕ) : Type :=
  {ℓ : H →ₗ[ℂ] ℂ // Sobolev₂ (lieSet ε) σ ℓ ∧ ∀ g ∈ UJset ε, ‖ℓ (σ g a)‖ ≤ wt N g}

variable [CompleteSpace H]

theorem orbit_bound (h : Std ε σ) {a : H} (ha : Sm ε σ a) (ha0 : a ≠ 0) (N : ℕ) {v : H} (hv : IsKFin ε σ v) :
    ∃ C, 0 ≤ C ∧ ∀ ℓ : Forms ε σ a N, ∀ g ∈ UJset ε, ‖ℓ.1 (σ g v)‖ ≤ C * wt N g := by
  obtain ⟨T, ⟨Z, C, hZ, hZG, hC, hT⟩, rfl⟩ := GlobalTheory.T.exists_averaged_operator_mapping_to_KFinite n ε H σ h a ha0 v hv
  obtain ⟨B, hB⟩ := (hZ.bddAbove_image (continuous_wt N).continuousOn)
  refine ⟨C * |B|, by positivity, fun ℓ g hg => ?_⟩
  have := avgBd_sobCont n ε H σ h T Z C hZ hZG hC hT Unit (fun _ => ℓ.1 ∘ₗ (σ g : H →ₗ[ℂ] H)) (fun _ => a)
    (fun _ => sobCont_translate h.1 ℓ.2.1 hg) (fun _ => ha) (fun _ => h.2.2.1 _ hv) (|B| * wt N g)
    (mul_nonneg (abs_nonneg _) (wt_pos N g).le) (fun y hy => by
      rw [Fintype.sum_unique]
      change ‖ℓ.1 (σ g (σ y a))‖ ≤ _
      rw [← sigma_mul h.1 hg (hZG hy), mul_comm |B|]
      refine (ℓ.2.2 _ (mul_mem_UJ hg (hZG hy))).trans ((wt_mul_le N g y).trans ?_)
      exact mul_le_mul_of_nonneg_left ((hB ⟨y, hy, rfl⟩).trans (le_abs_self B)) (wt_pos N g).le)
  rw [Fintype.sum_unique, ← mul_assoc] at this
  exact this

theorem hasDerivAt_coef (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {v : H} (hv : Sm ε σ v)
    {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n} (hg : g ∈ UJset ε) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ℓ (σ (g * NormedSpace.exp (t • X)) v))
      (ℓ (σ (g * NormedSpace.exp (s • X)) (dRep σ X v))) s := by
  have hs := mul_mem_UJ hg (exp_mem_UJ hX s)
  have h1 := h.hasDerivAt_sobFun ((sobFun_of_sobCont hℓ).translate h.1 hs) hv hX
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = ℓ (σ _ (σ _ v))
  rw [← sigma_mul h.1 hs (exp_mem_UJ hX _), mul_assoc, ← exp_add_smul, add_sub_cancel]

theorem taylor_bound (h : Std ε σ) {a : H} (ha : Sm ε σ a) (ha0 : a ≠ 0) (N : ℕ) {v : H} (hv : IsKFin ε σ v)
    {X : Mx n} (hX : X ∈ lieSet ε) :
    ∃ C, 0 ≤ C ∧ ∀ ℓ : Forms ε σ a N, ∀ g ∈ UJset ε, ∀ t : ℝ, |t| ≤ 1 →
      ‖ℓ.1 (σ (g * NormedSpace.exp (t • X)) v) - ℓ.1 (σ g v) - t • ℓ.1 (σ g (dRep σ X v))‖ ≤ C * wt N g * t ^ 2 := by
  have hv1 := isKFin_dRep n ε H σ h v hv X hX
  have hv2 := isKFin_dRep n ε H σ h _ hv1 X hX
  obtain ⟨C, hC, hb⟩ := orbit_bound h ha ha0 N hv2
  obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image
    ((continuous_wt N).comp (continuous_exp_smul X)).continuousOn)
  refine ⟨C * |B|, by positivity, fun ℓ g hg t ht => ?_⟩
  have := taylor_two (hasDerivAt_coef h ℓ.2.1 (h.2.2.1 _ hv) hX hg) (hasDerivAt_coef h ℓ.2.1 (h.2.2.1 _ hv1) hX hg)
    (K := C * |B| * wt N g) (fun s hs => by
      refine (hb ℓ _ (mul_mem_UJ hg (exp_mem_UJ hX s))).trans ?_
      rw [mul_assoc, mul_comm |B|]
      refine mul_le_mul_of_nonneg_left ((wt_mul_le N g _).trans ?_) hC
      exact mul_le_mul_of_nonneg_left ((hB ⟨s, abs_le.1 hs, rfl⟩).trans (le_abs_self B)) (wt_pos N g).le) ht
  simpa only [zero_smul, NormedSpace.exp_zero, mul_one] using this

theorem exists_map (h : Std ε σ) {a : H} (ha : Sm ε σ a) (ha0 : a ≠ 0) (N : ℕ) :
    ∃ T₀ : H →ₗ[ℂ] Bd (Forms ε σ a N × UJset ε), ∀ v, IsKFin ε σ v → ∀ i,
      T₀ v i = i.1.1 (σ i.2.1 v) / wt N i.2.1 := by
  let f : kfin ε σ →ₗ[ℂ] Bd (Forms ε σ a N × UJset ε) :=
    { toFun := fun v => mkBd (fun i => i.1.1 (σ i.2.1 v) / wt N i.2.1) (by
        obtain ⟨C, -, hC⟩ := orbit_bound h ha ha0 N v.2
        refine ⟨C, fun i => ?_⟩
        rw [norm_div, norm_wt, div_le_iff₀ (wt_pos _ _)]
        exact hC _ _ i.2.2)
      map_add' := fun v w => by ext i; simp [add_div]
      map_smul' := fun c v => by ext i; simp [mul_div_assoc] }
  obtain ⟨T, hT⟩ := LinearMap.exists_extend f
  refine ⟨T, fun v hv i => ?_⟩
  have : T v = f ⟨v, hv⟩ := LinearMap.congr_fun hT ⟨v, hv⟩
  rw [this]
  rfl

theorem unit_bound (hCW : GlobalTheory.Published.CasselmanWallach) (h : Std ε σ) {a : H} (ha : Sm ε σ a) (ha0 : a ≠ 0) (N : ℕ) :
    ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧
      ∀ ℓ : Forms ε σ a N, ∀ w, Sm ε σ w → ‖ℓ.1 w‖ ≤ C * sobNorm σ S w := by
  obtain ⟨T₀, hT₀⟩ := exists_map h ha ha0 N
  have key : ∀ v, IsKFin ε σ v → ∀ y ∈ UJset ε, ∀ i, rt ε _ N y (T₀ v) i = i.1.1 (σ (i.2.1 * y) v) / wt N i.2.1 := by
    intro v hv y hy i
    rw [rt_apply hy, hT₀ v hv]
    have := wt_ne N (i.2.1 * y)
    field_simp
  obtain ⟨T, hT1, hT2, S, C, hS, hC⟩ := GlobalTheory.T.casselmanWallach_extension_banach_target hCW n ε H σ h _ _ (modRep_rt ε (Forms ε σ a N) N) T₀
    (fun k hk v hv => by
      ext i
      rw [key v hv k (K_le_UJ hk), hT₀ _ (isKFin_translate hv hk), sigma_mul h.1 i.2.2 (K_le_UJ hk)])
    (fun X hX v hv => by
      obtain ⟨C, hC, hb⟩ := taylor_bound h ha ha0 N hv hX
      refine hasDerivAt_of_sq (K := C) fun t ht => lp.norm_le_of_forall_le (by positivity) fun i => ?_
      have e : (t • T₀ (dRep σ X v)) i = t • T₀ (dRep σ X v) i := rfl
      rw [lp.coeFn_sub, lp.coeFn_sub, Pi.sub_apply, Pi.sub_apply, e, key v hv _ (exp_mem_UJ hX _),
        key v hv _ (exp_mem_UJ hX _), hT₀ _ (isKFin_dRep n ε H σ h v hv X hX), zero_smul, NormedSpace.exp_zero, mul_one,
        ← smul_div_assoc, ← sub_div, ← sub_div, norm_div, norm_wt, div_le_iff₀ (wt_pos _ _), mul_right_comm]
      exact hb _ _ i.2.2 t ht)
  refine ⟨S, wt N (1 : Mx n) * |C|, hS, mul_nonneg (wt_pos _ _).le (abs_nonneg _), fun ℓ w hw => ?_⟩
  let ℓ' : H →ₗ[ℂ] ℂ :=
    { toFun := fun w => wt N (1 : Mx n) * T w (ℓ, ⟨1, one_mem_UJ ε⟩)
      map_add' := fun x y => by simp [mul_add]
      map_smul' := fun c x => by simp; ring }
  have hb : ∀ w, Sm ε σ w → ‖ℓ' w‖ ≤ wt N (1 : Mx n) * |C| * sobNorm σ S w := fun w hw => by
    change ‖(wt N (1 : Mx n) : ℂ) * T w (ℓ, ⟨1, one_mem_UJ ε⟩)‖ ≤ _
    rw [norm_mul, norm_wt, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((apply_le _ _).trans ((hC w hw).trans ?_)) (wt_pos _ _).le
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (sobNorm_nonneg _ _ _)
  obtain ⟨v, hv, hv0⟩ := h.2.2.2.2
  have h0 := h.eq_zero_of_orbit (sob_sub ℓ.2.1 (ℓ' := ℓ') ⟨S, _, hS, hb⟩) (h.2.2.1 v hv) hv0 (fun g hg => by
    change ℓ.1 (σ g v) - wt N (1 : Mx n) * T (σ g v) (ℓ, ⟨1, one_mem_UJ ε⟩) = 0
    rw [hT2 g hg v (h.2.2.1 v hv), hT1 v hv, key v hv g hg]
    have := wt_ne N (1 : Mx n)
    simp only [one_mul]
    field_simp
    ring) hw
  rw [LinearMap.sub_apply, sub_eq_zero] at h0
  rw [h0]
  exact hb w hw

end GlobalTheory.TypeSum.CoefLow

namespace GlobalTheory.TypeSum

open CoefLow in

theorem coefBound_of_casselmanWallach : GlobalTheory.Published.CasselmanWallach → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    CoefBound ε σ := by
  intro hCW n ε H _ _ _ σ h a ha ha0 N
  obtain ⟨S, C, hS, hC, hb⟩ := unit_bound hCW h ha ha0 N
  refine ⟨S, C, hS, hC, fun ℓ hℓ M hM hg w hw => ?_⟩
  rcases hM.eq_or_lt with rfl | hM
  · rw [h.eq_zero_of_orbit hℓ ha ha0 (fun g hg' => by simpa using hg g hg') hw]
    simp
  · have e : ∀ z : H, ‖((M : ℂ)⁻¹ • ℓ) z‖ = ‖ℓ z‖ / M := fun z => by
      rw [LinearMap.smul_apply, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hM.le, inv_mul_eq_div]
    have := hb ⟨(M : ℂ)⁻¹ • ℓ, sob_smul _ hℓ, fun g hg' => by
      rw [e, div_le_iff₀' hM]; exact hg g hg'⟩ w hw
    rw [e, div_le_iff₀ hM] at this
    rw [mul_right_comm]
    exact this

end GlobalTheory.TypeSum

end
