import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartUniformConstantsHalfPolydisc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulInvMulPosSemidefUniformBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurComplementBlockQuadraticLowerBound

open Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.PeriodLimit

def realVec (g : ℕ) : (Fin g → ℝ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun x := fun i => (x i : ℂ)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

@[simp] theorem realVec_apply {g : ℕ} (x : Fin g → ℝ) (i : Fin g) : realVec g x i = (x i : ℂ) := rfl

theorem hf_add_left {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (u u' w : Fin g → ℂ) :
    hermForm H (u + u') w = hermForm H u w + hermForm H u' w := by
  simp [hermForm, add_dotProduct]

theorem hf_add_right {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (u w w' : Fin g → ℂ) :
    hermForm H u (w + w') = hermForm H u w + hermForm H u w' := by
  simp [hermForm, mulVec_add, dotProduct_add]

theorem hf_smul_left {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (u w : Fin g → ℂ) :
    hermForm H (c • u) w = c * hermForm H u w := by
  simp [hermForm, smul_dotProduct]

theorem hf_smul_right {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (u w : Fin g → ℂ) :
    hermForm H u (c • w) = (starRingEnd ℂ) c * hermForm H u w := by
  simp [hermForm, star_smul, mulVec_smul, dotProduct_smul]

theorem exists_re_im {g : ℕ} (V : Submodule ℂ (Fin g → ℂ)) (N : Submodule ℝ (Fin g → ℝ))
    (hNV : ∀ x ∈ N, realVec g x ∈ V) (hdim : Module.finrank ℂ V ≤ Module.finrank ℝ N) (u : Fin g → ℂ) (hu : u ∈ V) :
    ∃ x ∈ N, ∃ y ∈ N, u = realVec g x + Complex.I • realVec g y := by
  let L : (N × N) →ₗ[ℝ] V :=
    { toFun := fun p => ⟨realVec g p.1 + Complex.I • realVec g p.2,
        V.add_mem (hNV _ p.1.2) (V.smul_mem _ (hNV _ p.2.2))⟩
      map_add' := fun p q => by ext i; simp; ring
      map_smul' := fun c p => by ext i; simp; ring }
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    have h : ∀ i, ((p.1 : Fin g → ℝ) i : ℂ) + Complex.I * ((p.2 : Fin g → ℝ) i : ℂ) = 0 := fun i => by
      simpa [L] using congrFun (congrArg Subtype.val hp) i
    ext i
    · simpa using congrArg Complex.re (h i)
    · simpa using congrArg Complex.im (h i)
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank ℝ V = 2 * Module.finrank ℂ V := finrank_real_of_complex V
  have h3 : Module.finrank ℝ (N × N) = Module.finrank ℝ V := by
    rw [Module.finrank_prod] at h1 ⊢; omega
  obtain ⟨p, hp⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h3).1 hinj ⟨u, hu⟩
  exact ⟨p.1, p.1.2, p.2, p.2.2, (congrArg Subtype.val hp).symm⟩

theorem bound_of_limit {Z : Type} (F : Filter Z) [F.NeBot] {g g' : ℕ} (G : Z → Matrix (Fin g) (Fin g) ℂ) (K : ℝ)
    (hK : ∀ᶠ z in F, ∀ u w, ‖hermForm (G z) u w‖ ≤ K * ‖u‖ * ‖w‖)
    (π : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (H' : Matrix (Fin g') (Fin g') ℂ)
    (hpos : ∀ w : Fin g' → ℂ, w ≠ 0 → 0 < (hermForm H' w w).re)
    (W : Submodule ℝ (Fin g → ℂ)) (hW : ∀ y, ∃ w ∈ W, π w = y)
    (hlim : ∀ v ∈ W, ∀ w ∈ W,
      Tendsto (fun z => (hermForm (G z) v w).im) F (𝓝 (hermForm H' (π v) (π w)).im))
    (N : Submodule ℝ (Fin g → ℝ)) (hNW : ∀ x ∈ N, realVec g x ∈ W)
    (hN : ∀ x ∈ N, ∀ w, Tendsto (fun z => hermForm (G z) (realVec g x) w) F (𝓝 0) ∧
      Tendsto (fun z => hermForm (G z) w (realVec g x)) F (𝓝 0))
    (hdim : Module.finrank ℂ (LinearMap.ker π) ≤ Module.finrank ℝ N) (v : Fin g → ℂ) :
    (hermForm H' (π v) (π v)).re ≤ K * ‖v‖ ^ 2 := by
  have hker : ∀ x ∈ N, realVec g x ∈ LinearMap.ker π := by
    intro x hx
    by_contra hne
    have hp := hpos _ hne
    obtain ⟨w, hw, hπ⟩ := hW ((-Complex.I) • π (realVec g x))
    have h1 := hlim _ (hNW x hx) _ hw
    have h2 := (Complex.continuous_im.tendsto _).comp (hN x hx w).1
    have h3 := tendsto_nhds_unique h1 h2
    rw [hπ, hf_smul_right] at h3
    simp at h3
    exact hp.ne' h3
  have hnull : ∀ u ∈ LinearMap.ker π, ∀ w, Tendsto (fun z => hermForm (G z) u w) F (𝓝 0) ∧
      Tendsto (fun z => hermForm (G z) w u) F (𝓝 0) := by
    intro u hu w
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_re_im _ N hker hdim u hu
    simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right]
    exact ⟨by simpa using (hN x hx w).1.add ((hN y hy w).1.const_mul Complex.I),
      by simpa using (hN x hx w).2.add ((hN y hy w).2.const_mul ((starRingEnd ℂ) Complex.I))⟩
  obtain ⟨w, hw, hπ⟩ := hW (π v)
  obtain ⟨w', hw', hπ'⟩ := hW (π (Complex.I • v))
  have h1 := hlim _ hw' _ hw
  have hk : w - v ∈ LinearMap.ker π := by simp [hπ]
  have hk' : w' - Complex.I • v ∈ LinearMap.ker π := by simp [hπ']
  have h2 := (Complex.continuous_im.tendsto _).comp ((hnull _ hk' w).1.add (hnull _ hk (Complex.I • v)).2)
  have h3 : Tendsto (fun z => (hermForm (G z) v v).re) F (𝓝 (hermForm H' (π v) (π v)).re) := by
    have h4 := h1.sub h2
    rw [hπ, hπ', map_smul, hf_smul_left] at h4
    simp only [Complex.I_mul_im, add_zero, Complex.zero_im, sub_zero] at h4
    refine h4.congr fun z => ?_
    have e : hermForm (G z) w' w = (hermForm (G z) (w' - Complex.I • v) w +
        hermForm (G z) (Complex.I • v) (w - v)) + Complex.I * hermForm (G z) v v := by
      rw [← hf_smul_left, add_assoc, ← hf_add_right, sub_add_cancel, ← hf_add_left, sub_add_cancel]
    simp only [Function.comp, e, Complex.add_im, Complex.I_mul_im]
    ring
  refine le_of_tendsto h3 (hK.mono fun z hz => ?_)
  have := (Complex.re_le_norm _).trans (hz v v)
  nlinarith

theorem lim_span {Z : Type} (F : Filter Z) {g g' : ℕ} (G : Z → Matrix (Fin g) (Fin g) ℂ) (K : ℝ)
    (hK : ∀ᶠ z in F, ∀ u w, ‖hermForm (G z) u w‖ ≤ K * ‖u‖ * ‖w‖)
    (π : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (H' : Matrix (Fin g') (Fin g') ℂ) (Λ : Set (Fin g → ℂ))
    (h : ∀ v ∈ Λ, ∀ w ∈ Λ, ∃ ζ ζ' : Z → Fin g → ℂ, Tendsto ζ F (𝓝 v) ∧ Tendsto ζ' F (𝓝 w) ∧
      ∀ᶠ z in F, (hermForm (G z) (ζ z) (ζ' z)).im = (hermForm H' (π v) (π w)).im) :
    ∀ v ∈ Submodule.span ℝ Λ, ∀ w ∈ Submodule.span ℝ Λ,
      Tendsto (fun z => (hermForm (G z) v w).im) F (𝓝 (hermForm H' (π v) (π w)).im) := by
  intro v hv w hw
  have rs : ∀ (c : ℝ) (u : Fin g → ℂ), c • u = (c : ℂ) • u := fun c u => by ext i; simp
  induction hv, hw using Submodule.span_induction₂ with
  | mem_mem v w hv hw =>
    obtain ⟨ζ, ζ', h1, h2, h3⟩ := h v hv w hw
    have t1 : Tendsto (fun z => hermForm (G z) (v - ζ z) w) F (𝓝 0) := by
      refine squeeze_zero_norm' (hK.mono fun z hz => hz _ _) ?_
      simpa using (((tendsto_const_nhds (x := v)).sub h1).norm.const_mul K).mul_const ‖w‖
    have t2 : Tendsto (fun z => hermForm (G z) (ζ z) (w - ζ' z)) F (𝓝 0) := by
      refine squeeze_zero_norm' (hK.mono fun z hz => hz _ _) ?_
      simpa using (h1.norm.const_mul K).mul ((tendsto_const_nhds (x := w)).sub h2).norm
    have t3 := ((Complex.continuous_im.tendsto _).comp (t1.add t2)).add_const (hermForm H' (π v) (π w)).im
    simp only [add_zero, Complex.zero_im, zero_add] at t3
    refine t3.congr' (h3.mono fun z hz => ?_)
    simp only [Function.comp]
    rw [← hz, ← Complex.add_im, add_assoc, ← hf_add_right, sub_add_cancel, ← hf_add_left, sub_add_cancel]
  | zero_left => simpa [hermForm] using tendsto_const_nhds
  | zero_right => simpa [hermForm] using tendsto_const_nhds
  | add_left x y z _ _ _ h1 h2 => simpa only [map_add, hf_add_left, Complex.add_im] using h1.add h2
  | add_right x y z _ _ _ h1 h2 => simpa only [map_add, hf_add_right, Complex.add_im] using h1.add h2
  | smul_left c x y _ _ h1 =>
    simpa only [rs, map_smul, hf_smul_left, Complex.im_ofReal_mul] using h1.const_mul c
  | smul_right c x y _ _ h1 =>
    simpa only [rs, map_smul, hf_smul_right, Complex.conj_ofReal, Complex.im_ofReal_mul] using h1.const_mul c

theorem mem_of_int_kernel {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) (U : Submodule ℝ (Fin g → ℝ))
    (hU : ∀ m : Fin g → ℤ, S *ᵥ m = 0 → (fun i => (m i : ℝ)) ∈ U) (y : Fin g → ℝ)
    (hy : S.map (Int.cast : ℤ → ℝ) *ᵥ y = 0) : y ∈ U := by
  set A : Matrix (Fin g) (Fin g) ℚ := S.map (Int.cast : ℤ → ℚ) with hA
  obtain ⟨s, hs⟩ := (toLin' A).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
  obtain ⟨T, hT⟩ := s.exists_extend
  have h1 : toLin' A ∘ₗ T ∘ₗ toLin' A = toLin' A := by
    refine LinearMap.ext fun x => ?_
    have a1 := LinearMap.congr_fun hT ((toLin' A).rangeRestrict x)
    have a2 := congrArg Subtype.val (LinearMap.congr_fun hs ((toLin' A).rangeRestrict x))
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at a1 a2 ⊢
    exact (congrArg _ a1).trans a2
  set P : Matrix (Fin g) (Fin g) ℚ := 1 - LinearMap.toMatrix' T * A with hP
  have h2 : A * P = 0 := by
    have := congrArg LinearMap.toMatrix' h1
    simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at this
    rw [hP, Matrix.mul_sub, Matrix.mul_one, this, sub_self]
  have h3 : P.map (Rat.castHom ℝ) *ᵥ y = y := by
    have e : A.map (Rat.castHom ℝ) = S.map (Int.cast : ℤ → ℝ) := by ext i j; simp [hA]
    rw [hP, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), sub_mulVec,
      one_mulVec, ← mulVec_mulVec, e, hy, mulVec_zero, sub_zero]
  have h4 : ∀ j, (fun i => (P i j : ℝ)) ∈ U := by
    intro j
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) (fun i => P i j)
    choose m hm using hb
    have hb0 : ((b : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero b
    have hm' : ∀ i, (m i : ℚ) = (b : ℤ) * P i j := fun i => by simpa using hm i
    have h5 : S *ᵥ m = 0 := by
      ext i
      have := congrFun (congrFun h2 i) j
      simp only [mul_apply, hA, map_apply, Matrix.zero_apply] at this
      have h6 : (((S *ᵥ m) i : ℤ) : ℚ) = ((b : ℤ) : ℚ) * ∑ k, (S i k : ℚ) * P k j := by
        simp only [mulVec, dotProduct, Finset.mul_sum]
        push_cast
        exact Finset.sum_congr rfl fun k _ => by rw [hm']; ring
      rw [this, mul_zero] at h6
      exact_mod_cast h6
    have := U.smul_mem (((b : ℤ) : ℝ)⁻¹) (hU m h5)
    convert this using 1
    ext i
    have h7 : (m i : ℝ) = ((b : ℤ) : ℝ) * (P i j : ℝ) := by exact_mod_cast congrArg (Rat.cast : ℚ → ℝ) (hm' i)
    simp only [Pi.smul_apply, smul_eq_mul, h7]
    field_simp
  rw [← h3]
  have e : P.map (Rat.castHom ℝ) *ᵥ y = ∑ j, y j • fun i => (P i j : ℝ) := by
    ext i; simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [e]
  exact U.sum_mem fun j _ => U.smul_mem _ (h4 j)

theorem le_finrank_range {g : ℕ} (S : Matrix (Fin g) (Fin g) ℝ) (τ : Matrix (Fin g) (Fin g) ℂ)
    (W : Submodule ℝ (Fin g → ℂ)) (h1 : ∀ x, realVec g x ∈ W) (h2 : ∀ y, S *ᵥ y = 0 → τ *ᵥ realVec g y ∈ W)
    (h3 : ∀ y, S *ᵥ y = 0 → τ.map Complex.im *ᵥ y = 0 → y = 0) (k : ℕ) (hk : Module.finrank ℝ W + k ≤ 2 * g) :
    k ≤ Module.finrank ℝ (LinearMap.range S.mulVecLin) := by
  let L : ((Fin g → ℝ) × LinearMap.ker S.mulVecLin) →ₗ[ℝ] W :=
    { toFun := fun p => ⟨realVec g p.1 + τ *ᵥ realVec g p.2, W.add_mem (h1 _) (h2 _ p.2.2)⟩
      map_add' := fun p q => by ext i; simp [mulVec_add]; ring
      map_smul' := fun c p => by ext i; simp [mulVec_smul] }
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    have h : realVec g p.1 + τ *ᵥ realVec g p.2 = 0 := congrArg Subtype.val hp
    have h' : (p.2 : Fin g → ℝ) = 0 := by
      refine h3 _ p.2.2 ?_
      ext i
      simpa [mulVec, dotProduct, Complex.im_sum] using congrArg Complex.im (congrFun h i)
    rw [h', map_zero, mulVec_zero, add_zero] at h
    refine Prod.ext ?_ (Subtype.ext h')
    ext i
    simpa using congrFun h i
  have a1 := LinearMap.finrank_le_finrank_of_injective hinj
  have a2 := LinearMap.finrank_range_add_finrank_ker S.mulVecLin
  rw [Module.finrank_prod] at a1
  simp only [Module.finrank_fin_fun] at a1 a2
  omega

theorem isUnit_det_of_lower {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) : IsUnit Y.det := by
  rw [isUnit_iff_ne_zero, Ne, ← exists_mulVec_eq_zero_iff]
  rintro ⟨v, hv, h0⟩
  have h1 := h v
  rw [h0, dotProduct_zero] at h1
  have h2 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)
  exact hv (dotProduct_self_eq_zero.1 (le_antisymm (by nlinarith) h2))

theorem abs_inv_le {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) (j k : Fin g) : |Y⁻¹ j k| ≤ 1 / c := by
  set u : Fin g → ℝ := Y⁻¹ *ᵥ Pi.single k 1 with hu
  have h1 := h u
  have e : Y *ᵥ u = Pi.single k 1 := by
    rw [hu, mulVec_mulVec, mul_nonsing_inv _ (isUnit_det_of_lower hc h), one_mulVec]
  rw [e, dotProduct_single, mul_one] at h1
  have hs : ∀ i, u i * u i ≤ u ⬝ᵥ u := fun i =>
    Finset.single_le_sum (f := fun j => u j * u j) (fun j _ => mul_self_nonneg (u j)) (Finset.mem_univ i)
  have hj : Y⁻¹ j k = u j := by simp [hu]
  rw [hj, le_div_iff₀ hc]
  have a1 := hs j
  have a2 := hs k
  have a3 : c * u k ≤ 1 := by
    nlinarith [sq_nonneg (c * u k - 1),
      mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left a2 hc.le).trans h1) hc.le]
  have a4 : (u j * c) ^ 2 ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left a1 hc.le).trans h1) hc.le]
  have := abs_le_one_iff_mul_self_le_one.2 (show (u j * c) * (u j * c) ≤ 1 by nlinarith)
  rwa [abs_mul, abs_of_pos hc] at this

theorem norm_hf_le {g : ℕ} {G : Matrix (Fin g) (Fin g) ℂ} {K : ℝ} (h : ∀ j k, ‖G j k‖ ≤ K)
    (u w : Fin g → ℂ) : ‖hermForm G u w‖ ≤ (g * g * K) * ‖u‖ * ‖w‖ := by
  simp only [hermForm, dotProduct, mulVec, Finset.mul_sum]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun _ => g * (K * ‖u‖ * ‖w‖)) fun j _ => ?_).trans_eq
    (by simp; ring))
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun _ => K * ‖u‖ * ‖w‖) fun k _ => ?_).trans_eq
    (by simp))
  have h0 : 0 ≤ K := (norm_nonneg _).trans (h j k)
  rw [norm_mul, norm_mul, Pi.star_apply, norm_star]
  calc ‖u j‖ * (‖G j k‖ * ‖w k‖) ≤ ‖u‖ * (K * ‖w‖) := by
        gcongr
        exacts [norm_le_pi_norm u j, h j k, norm_le_pi_norm w k]
    _ = _ := by ring

theorem inv_map_ofReal {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (h : IsUnit Y.det) :
    (Y.map Complex.ofReal)⁻¹ = (Y⁻¹).map Complex.ofReal := by
  refine inv_eq_right_inv ?_
  have := (Matrix.map_mul (L := Y) (M := Y⁻¹) (f := Complex.ofRealHom)).symm
  rw [mul_nonsing_inv _ h, Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this

theorem null_of_tendsto {Z : Type} (F : Filter Z) {g : ℕ} (G : Z → Matrix (Fin g) (Fin g) ℂ)
    (R : Z → Matrix (Fin g) (Fin g) ℝ) (d : ℝ)
    (hG : ∀ᶠ z in F, G z = (d : ℂ) • (R z).map Complex.ofReal ∧ (R z).IsSymm) (x : Fin g → ℝ)
    (hx : Tendsto (fun z => R z *ᵥ x) F (𝓝 0)) (w : Fin g → ℂ) :
    Tendsto (fun z => hermForm (G z) (realVec g x) w) F (𝓝 0) ∧
      Tendsto (fun z => hermForm (G z) w (realVec g x)) F (𝓝 0) := by
  have hc : ∀ w : Fin g → ℂ, Tendsto (fun z => (d : ℂ) * (w ⬝ᵥ realVec g (R z *ᵥ x))) F (𝓝 0) := fun w => by
    have : Continuous fun y : Fin g → ℝ => (d : ℂ) * (w ⬝ᵥ realVec g y) := by
      simp only [dotProduct, realVec_apply]; fun_prop
    simpa [Function.comp_def] using (this.tendsto 0).comp hx
  refine ⟨(hc (star w)).congr' (hG.mono fun z hz => ?_), (hc w).congr' (hG.mono fun z hz => ?_)⟩
  · simp only [hz.1, hermForm, dotProduct, mulVec, realVec_apply, Finset.mul_sum, Matrix.smul_apply, map_apply,
      smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hz.2.apply j k]; ring
  · simp only [hz.1, hermForm, dotProduct, mulVec, realVec_apply, Finset.mul_sum, Matrix.smul_apply, map_apply,
      smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring

theorem im_log_div (L w : ℂ) (h : Complex.exp L = w) :
    (L / (2 * Real.pi * Complex.I)).im = GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog w := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : L / (2 * Real.pi * Complex.I) = ((-1 / (2 * Real.pi) : ℝ) : ℂ) * (L * Complex.I) := by
    push_cast; field_simp; simp
  rw [e, Complex.im_ofReal_mul, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog, ← h, Complex.norm_exp, Real.log_exp]
  simp; ring

open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram in

theorem limit_form_bounded : ∀ (n a g rk : ℕ) (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (d : ℝ) (Dn : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B → 0 < d → 0 < Dn → ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 ≤ C ∧ ∀ z₀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n ρ, ∀ (Λ : Set (Fin g → ℂ)) (g' : ℕ) (π : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (H' : Matrix (Fin g') (Fin g') ℂ), H'.IsHermitian → (∀ w : Fin g' → ℂ, w ≠ 0 → 0 < (hermForm H' w w).re) → Submodule.span ℝ (π '' Λ) = ⊤ → Module.finrank ℝ (Submodule.span ℝ Λ) + Module.finrank ℂ (LinearMap.ker π) ≤ 2 * g → (∀ v ∈ Λ, ∀ w ∈ Λ, ∃ ζ ζ' : (Fin n → ℂ) → Fin g → ℂ, ContinuousAt ζ z₀ ∧ ContinuousAt ζ' z₀ ∧ ζ z₀ = v ∧ ζ' z₀ = w ∧ ∀ᶠ z in 𝓝 z₀, (∀ i : Fin a, z (Fin.castLE ha i) ≠ 0) → (hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B z)⁻¹) (ζ z) (ζ' z)).im = (hermForm H' (π v) (π w)).im) → (∃ large₂ : Fin a → ℂ, (∀ i, z₀ (Fin.castLE ha i) ≠ 0 → Complex.exp (large₂ i) = z₀ (Fin.castLE ha i)) ∧ ∀ m m' : Fin g → ℤ, (∀ i, z₀ (Fin.castLE ha i) = 0 → B i *ᵥ m' = 0) → (Dn : ℂ) • ((fun i => (m i : ℂ)) + GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period τ₀ B z₀ large₂ *ᵥ fun i => (m' i : ℂ)) ∈ Λ) → ∀ v : Fin g → ℂ, (hermForm H' (π v) (π v)).re ≤ C * ‖v‖ ^ 2 := by
  intro n a g rk ha τ₀ B d Dn hP hd hDn
  classical
  obtain ⟨T₀, c₁, C₁, M, β, hT₀, hc₁, -, -, -, hY'⟩ :=
    GlobalTheory.UnifConsts.uniform_consts n a g rk τ₀ B GlobalTheory.schur_block_lower_bound hP
  obtain ⟨W, hW'⟩ := GlobalTheory.smul_inv_mul_posSemidef_uniform_bound g a (fun i => (B i).map (Int.cast : ℤ → ℝ)) c₁ C₁ hc₁
    hP.psd
  have hBnn : ∀ i (x : Fin g → ℝ), 0 ≤ x ⬝ᵥ ((B i).map (Int.cast : ℤ → ℝ)) *ᵥ x := fun i x => by
    simpa using (posSemidef_iff_dotProduct_mulVec.1 (hP.psd i)).2 x
  have hBsymm : ∀ i (j k : Fin g), (B i k j : ℝ) = B i j k := fun i j k => by
    simpa using (hP.psd i).isHermitian.apply j k
  set ρ : ℝ := min (1 / 2) (Real.exp (-(4 * Real.pi * T₀))) with hρ
  have hρ0 : 0 < ρ := lt_min (by norm_num) (Real.exp_pos _)
  have hρ2 : ρ ≤ 1 / 2 := min_le_left _ _
  have hρ1 : ρ ≤ 1 := hρ2.trans (by norm_num)
  have ht : ∀ w : ℂ, w ≠ 0 → ‖w‖ < ρ → 2 * T₀ < tlog w := by
    intro w hw0 hw
    have h0 : 0 < ‖w‖ := norm_pos_iff.2 hw0
    have h1 : ‖w‖ < Real.exp (-(4 * Real.pi * T₀)) := hw.trans_le (min_le_right _ _)
    have h2 : Real.log ‖w‖ < -(4 * Real.pi * T₀) := by
      rw [← Real.log_exp (-(4 * Real.pi * T₀))]; exact Real.log_lt_log h0 h1
    rw [tlog, lt_div_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hdec : ∀ (z : Fin n → ℂ) (t : Fin a → ℝ), (τ₀ z).map Complex.im + ∑ i, t i • (B i).map (Int.cast : ℤ → ℝ) =
      ((τ₀ z).map Complex.im + T₀ • ∑ i, (B i).map (Int.cast : ℤ → ℝ))
      + ∑ i, (t i - T₀) • (B i).map (Int.cast : ℤ → ℝ) := fun z t => by
    simp only [sub_smul, Finset.sum_sub_distrib, Finset.smul_sum]; abel
  have hlow : ∀ z ∈ polydisc n ρ, ∀ (t : Fin a → ℝ) (x : Fin g → ℝ),
      (∀ i, T₀ ≤ t i ∨ (B i).map (Int.cast : ℤ → ℝ) *ᵥ x = 0) →
      c₁ * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((τ₀ z).map Complex.im + ∑ i, t i • (B i).map (Int.cast : ℤ → ℝ)) *ᵥ x := by
    intro z hz t x h
    rw [hdec, add_mulVec, dotProduct_add, sum_mulVec, dotProduct_sum]
    have h1 := (hY' z fun k => (hz k).trans_le hρ2).2.1 x
    have h2 : 0 ≤ ∑ i, x ⬝ᵥ ((t i - T₀) • (B i).map (Int.cast : ℤ → ℝ)) *ᵥ x := by
      refine Finset.sum_nonneg fun i _ => ?_
      rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
      rcases h i with h | h
      · exact mul_nonneg (by linarith) (hBnn i x)
      · simp [h]
    linarith
  refine ⟨ρ, g * g * (d * (1 / c₁)), hρ0, hρ1, by positivity, ?_⟩
  intro z₀ hz₀ Λ g' π H' _ hpos hspan hdim hlim ⟨large₂, hLg, hΛ⟩
  let F : Filter (Fin n → ℂ) := 𝓝[{z | ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0}] z₀
  haveI : F.NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.1 (Dense.mono (s₁ := Set.pi Set.univ fun _ => {0}ᶜ) ?_ ?_ z₀)
    · exact fun z hz i => hz _ trivial
    · exact dense_pi Set.univ fun _ _ => dense_compl_singleton 0
  have hF : ∀ᶠ z in F, z ∈ punctured ha ρ := by
    have ho : IsOpen (polydisc n ρ) := by
      simp only [polydisc, Set.setOf_forall]
      exact isOpen_iInter_of_finite fun k => isOpen_lt (by fun_prop) continuous_const
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ho.mem_nhds hz₀), self_mem_nhdsWithin] with z h1 h2 using ⟨h1, h2⟩
  have hYlow : ∀ z ∈ punctured ha ρ, ∀ x, c₁ * (x ⬝ᵥ x) ≤ x ⬝ᵥ imPeriod ha τ₀ B z *ᵥ x := fun z hz x =>
    hlow z hz.1 _ x fun i => Or.inl (by linarith [ht _ (hz.2 i) (hz.1 _)])
  have hG : ∀ᶠ z in F, (d : ℂ) • (hodgeGram ha τ₀ B z)⁻¹ = (d : ℂ) • ((imPeriod ha τ₀ B z)⁻¹).map Complex.ofReal ∧
      ((imPeriod ha τ₀ B z)⁻¹).IsSymm := hF.mono fun z hz => by
    refine ⟨by rw [hodgeGram, inv_map_ofReal (isUnit_det_of_lower hc₁ (hYlow z hz))], IsSymm.inv ?_⟩
    exact IsSymm.ext fun j k => by
      simp [imPeriod, Matrix.sum_apply, hBsymm, (hP.symm z fun k => (hz.1 k).trans_le hρ1).apply]
  have hK : ∀ᶠ z in F, ∀ u w, ‖hermForm ((d : ℂ) • (hodgeGram ha τ₀ B z)⁻¹) u w‖ ≤
      (g * g * (d * (1 / c₁))) * ‖u‖ * ‖w‖ := (hF.and hG).mono fun z hz => norm_hf_le fun j k => by
    rw [hz.2.1, Matrix.smul_apply, map_apply, smul_eq_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hd.le]
    exact mul_le_mul_of_nonneg_left (abs_inv_le hc₁ (hYlow z hz.1) j k) hd.le
  set S : Matrix (Fin g) (Fin g) ℤ := ∑ i ∈ Finset.univ.filter fun i => z₀ (Fin.castLE ha i) = 0, B i with hS
  have hSR : S.map (Int.cast : ℤ → ℝ) =
      ∑ i ∈ Finset.univ.filter fun i => z₀ (Fin.castLE ha i) = 0, (B i).map (Int.cast : ℤ → ℝ) := by
    ext j k; simp [hS, Matrix.sum_apply]
  have hker : ∀ y : Fin g → ℝ, S.map (Int.cast : ℤ → ℝ) *ᵥ y = 0 → ∀ i, z₀ (Fin.castLE ha i) = 0 →
      (B i).map (Int.cast : ℤ → ℝ) *ᵥ y = 0 := by
    intro y hy i hi
    have h1 := congrArg (y ⬝ᵥ ·) hy
    simp only [hSR, sum_mulVec, dotProduct_sum, dotProduct_zero] at h1
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hBnn i y).1 h1 i (by simp [hi])
    exact ((hP.psd i).dotProduct_mulVec_zero_iff y).1 (by simpa using h2)
  have hDn' : (Dn : ℝ) ≠ 0 := by exact_mod_cast hDn.ne'
  have hΛ' : ∀ u : Fin g → ℂ, (Dn : ℂ) • u ∈ Λ → u ∈ Submodule.span ℝ Λ := fun u hu => by
    convert (Submodule.span ℝ Λ).smul_mem (Dn : ℝ)⁻¹ (Submodule.subset_span hu) using 1
    have : (Dn : ℂ) ≠ 0 := by exact_mod_cast hDn.ne'
    ext i; simp [this]
  have hW1 : ∀ x, realVec g x ∈ Submodule.span ℝ Λ := fun x =>
    mem_of_int_kernel 0 ((Submodule.span ℝ Λ).comap (realVec g)) (fun m _ => hΛ' _ (by
      convert hΛ m 0 (fun i _ => mulVec_zero _) using 2
      ext i; simp [mulVec, dotProduct])) x (by simp)
  have hW2 : ∀ y, S.map (Int.cast : ℤ → ℝ) *ᵥ y = 0 → period τ₀ B z₀ large₂ *ᵥ realVec g y ∈ Submodule.span ℝ Λ :=
    fun y hy => mem_of_int_kernel S ((Submodule.span ℝ Λ).comap
      (((period τ₀ B z₀ large₂).mulVecLin.restrictScalars ℝ) ∘ₗ realVec g)) (fun m hm => hΛ' _ (by
        have hm' : S.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => (m i : ℝ)) = 0 := by
          ext i
          have := congrArg (Int.cast : ℤ → ℝ) (congrFun hm i)
          simpa [mulVec, dotProduct] using this
        convert hΛ 0 m (fun i hi => ?_) using 2
        · ext i; simp [mulVec, dotProduct]
        · ext j
          have := congrFun (hker _ hm' i hi) j
          simp only [mulVec, dotProduct, map_apply, Pi.zero_apply] at this ⊢
          exact_mod_cast this)) y hy
  have hW3 : ∀ y, S.map (Int.cast : ℤ → ℝ) *ᵥ y = 0 → (period τ₀ B z₀ large₂).map Complex.im *ᵥ y = 0 → y = 0 := by
    intro y hy h0
    have e : (period τ₀ B z₀ large₂).map Complex.im = (τ₀ z₀).map Complex.im +
        ∑ i, (large₂ i / (2 * Real.pi * Complex.I)).im • (B i).map (Int.cast : ℤ → ℝ) := by
      ext j k
      simp [period, Matrix.sum_apply, Complex.im_sum, Complex.mul_im]
    have h1 := hlow z₀ hz₀ (fun i => (large₂ i / (2 * Real.pi * Complex.I)).im) y fun i => by
      by_cases hi : z₀ (Fin.castLE ha i) = 0
      · exact Or.inr (hker y hy i hi)
      · left
        rw [im_log_div _ _ (hLg i hi)]
        linarith [ht _ hi (hz₀ _)]
    rw [← e, h0, dotProduct_zero] at h1
    have h2 : 0 ≤ y ⬝ᵥ y := Finset.sum_nonneg fun j _ => mul_self_nonneg (y j)
    exact dotProduct_self_eq_zero.1 (le_antisymm (by nlinarith) h2)
  have hnull : ∀ i, z₀ (Fin.castLE ha i) = 0 → ∀ x : Fin g → ℝ,
      Tendsto (fun z => (imPeriod ha τ₀ B z)⁻¹ *ᵥ ((B i).map (Int.cast : ℤ → ℝ) *ᵥ x)) F (𝓝 0) := by
    intro i hi x
    have t1 : Tendsto (fun z : Fin n → ℂ => ‖z (Fin.castLE ha i)‖) F (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, hF.mono fun z hz => norm_ne_zero_iff.2 (hz.2 i)⟩
      have : Continuous fun z : Fin n → ℂ => ‖z (Fin.castLE ha i)‖ := by fun_prop
      simpa [hi] using (this.tendsto z₀).mono_left (nhdsWithin_le_nhds : F ≤ 𝓝 z₀)
    have t2 : Tendsto (fun z : Fin n → ℂ => tlog (z (Fin.castLE ha i)) - T₀) F atTop :=
      tendsto_atTop_add_const_right F (-T₀) ((tendsto_neg_atBot_atTop.comp
        (Real.tendsto_log_nhdsNE_zero.comp t1)).atTop_div_const (by positivity))
    refine squeeze_zero_norm' (a := fun z => (tlog (z (Fin.castLE ha i)) - T₀)⁻¹ * (W * ‖x‖))
      (hF.mono fun z hz => ?_) (by simpa using t2.inv_tendsto_atTop.mul_const (W * ‖x‖))
    have hp : ∀ l, 0 < tlog (z (Fin.castLE ha l)) - T₀ := fun l => by linarith [ht _ (hz.2 l) (hz.1 _)]
    have hz2 := hY' z fun k => (hz.1 k).trans_le hρ2
    have := hW' _ (fun l => tlog (z (Fin.castLE ha l)) - T₀) hz2.1 hz2.2.1 hz2.2.2.1 hp i x
    beta_reduce at this
    rw [← hdec z, smul_mulVec, norm_smul, Real.norm_of_nonneg (hp i).le, ← mulVec_mulVec] at this
    exact (le_inv_mul_iff₀ (hp i)).2 this
  refine bound_of_limit F (fun z => (d : ℂ) • (hodgeGram ha τ₀ B z)⁻¹) _ hK π H' hpos (Submodule.span ℝ Λ)
    (fun y => ?_) (lim_span F _ _ hK π H' Λ fun v hv w hw => ?_)
    (LinearMap.range (S.map (Int.cast : ℤ → ℝ)).mulVecLin) (fun x _ => hW1 x) ?_
    (le_finrank_range _ _ _ hW1 hW2 hW3 _ hdim)
  · have h1 : y ∈ (Submodule.span ℝ Λ).map (π.restrictScalars ℝ) := by
      rw [Submodule.map_span]
      exact hspan ▸ Submodule.mem_top
    exact h1
  · obtain ⟨ζ, ζ', h1, h2, rfl, rfl, h3⟩ := hlim v hv w hw
    exact ⟨ζ, ζ', h1.tendsto.mono_left nhdsWithin_le_nhds, h2.tendsto.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_iff.2 h3⟩
  · rintro _ ⟨x, rfl⟩ w
    refine null_of_tendsto F _ _ d hG _ ?_ w
    simp only [mulVecLin_apply, hSR, sum_mulVec, mulVec_sum]
    simpa using tendsto_finset_sum (Finset.univ.filter fun i => z₀ (Fin.castLE ha i) = 0)
      fun i hi => hnull i (Finset.mem_filter.1 hi).2 x

end GlobalTheory.PeriodLimit
