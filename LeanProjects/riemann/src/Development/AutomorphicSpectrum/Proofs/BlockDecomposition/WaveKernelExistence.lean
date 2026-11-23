import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.WaveKer

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Local

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_germ (X : Mat n) {f : Mat n → V} {x : Mat n} (h : f =ᶠ[𝓝 x] 0) :
    Rd X f =ᶠ[𝓝 x] 0 := by
  filter_upwards [h.eventuallyEq_nhds] with y hy
  simp only [Rd, Pi.zero_apply]
  rw [hy.fderiv_eq]
  have : fderiv ℝ (0 : Mat n → V) y = 0 := by
    simpa using fderiv_const_apply (𝕜 := ℝ) (x := y) (0 : V)
  rw [this]
  rfl

theorem Eu_germ (s : Bool) (a b : Fin n) {f : Mat n → V} {x : Mat n} (h : f =ᶠ[𝓝 x] 0) :
    Eu s a b f =ᶠ[𝓝 x] 0 := by
  filter_upwards [Rd_germ (Matrix.single a b 1) h, Rd_germ (Matrix.single a b Complex.I) h]
    with y h1 h2
  simp only [Eu, Pi.smul_apply, Pi.add_apply, h1, h2, Pi.zero_apply, smul_zero, add_zero]

theorem Epow_germ (s : Bool) (m : ℕ) (a b : Fin n) {f : Mat n → V} {x : Mat n}
    (h : f =ᶠ[𝓝 x] 0) : Epow s m a b f =ᶠ[𝓝 x] 0 := by
  induction m generalizing a b with
  | zero =>
    by_cases hab : a = b
    · simpa [Epow, hab] using h
    · simp [Epow, hab]
  | succ m ih =>
    have : ∀ᶠ y in 𝓝 x, ∀ c, Eu s a c (Epow s m c b f) y = 0 :=
      eventually_all.2 fun c => Eu_germ s a c (ih c b)
    filter_upwards [this] with y hy
    simp [Epow, Finset.sum_apply, hy]

theorem gel_germ (s : Bool) (m : ℕ) {f : Mat n → V} {x : Mat n} (h : f =ᶠ[𝓝 x] 0) :
    gel s m f =ᶠ[𝓝 x] 0 := by
  have : ∀ᶠ y in 𝓝 x, ∀ a, Epow s m a a f y = 0 :=
    eventually_all.2 fun a => Epow_germ s m a a h
  filter_upwards [this] with y hy
  simp [gel, Finset.sum_apply, hy]

theorem zOp_germ (w : List (Bool × ℕ)) {f : Mat n → V} {x : Mat n} (h : f =ᶠ[𝓝 x] 0) :
    zOp w f =ᶠ[𝓝 x] 0 := by
  induction w with
  | nil => simpa [zOp] using h
  | cons p w ih => exact gel_germ p.1 p.2 ih

end Local

theorem one_mem_GLs (n : ℕ) : (1 : Mat n) ∈ GLs n := by simp [GLs]

theorem mul_mem_GLs {n : ℕ} {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, det_mul] at *
  exact mul_ne_zero hx hy

theorem unitary_mem_GLs {n : ℕ} (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n := by
  intro h
  have h1 := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 k.2)
  rw [det_mul, h, mul_zero, det_one] at h1
  exact zero_ne_one h1

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous fun g : Mat n => g.det := continuous_id.matrix_det
  exact isOpen_ne.preimage hc

theorem lg_one_nonneg (hL : LgFacts) (n : ℕ) : 0 ≤ lg (1 : Mat n) := by
  have h := (hL n).1 1 (one_mem_GLs n) 1 (one_mem_GLs n)
  rw [one_mul] at h
  linarith

theorem ker_support (hL : LgFacts) (hE : WaveEx) (hU : KerUniq) {n : ℕ}
    [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (c₀ : ℝ)
    (hc : ∀ (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → ∀ (t : ℝ), ∀ x ∈ GLs n,
      (∀ y ∈ GLs n, lg y ≤ c₀ * (1 + |t|) → u 0 (x * y) = 0) → u t x = 0)
    {w : List (Bool × ℕ)} {g : ℝ → ℝ} {T : ℝ} {k : Mat n → (E.V →L[ℂ] E.V)} (hT : 0 ≤ T)
    (hg : IsBump g T) (hk : IsKer μ E w g k) {y : Mat n} (hy : y ∈ GLs n)
    (hlt : (max c₀ 0 + lg (1 : Mat n) + 1) * (1 + T) < lg y) : k y = 0 := by
  obtain ⟨hsub, -, hinv, hsm, -, -, -⟩ := hL n
  have hL0 := lg_one_nonneg hL n
  have hM0 : 0 ≤ max c₀ 0 := le_max_right _ _
  have hGo := isOpen_GLs n
  set A : ℝ := (max c₀ 0 + lg (1 : Mat n) + 1) * (1 + T) with hA
  have hUo : IsOpen (GLs n ∩ lg ⁻¹' Set.Ioi A) :=
    hsm.continuousOn.isOpen_inter_preimage hGo isOpen_Ioi
  refine hU n μ E k (GLs n ∩ lg ⁻¹' Set.Ioi A) hUo Set.inter_subset_left ?_
    hk.1.continuousOn ?_ ?_ y ⟨hy, hlt⟩
  · intro z hz k₂
    refine ⟨mul_mem_GLs hz.1 (unitary_mem_GLs k₂), ?_⟩
    have h := hinv z hz.1 1 k₂
    simp only [OneMemClass.coe_one, one_mul] at h
    simpa [h] using hz.2
  · intro z hz k₂
    have h := hk.2.2.1 z hz 1 k₂
    simpa using h
  · intro f hf _ hoff
    obtain ⟨u, hu, hu0⟩ := hE n E f hf
    have hact : act μ E k f 1 = act μ E k (u 0) 1 := by
      simp only [act]
      congr 1
      funext z
      rw [one_mul, hu0 _ (val_mem_GLs z)]
    have hzero : ∀ x ∈ GLs n, lg x < lg (1 : Mat n) + 1 → ∀ t, |t| ≤ T → u t x = 0 := by
      intro x hx hlx t ht
      refine hc E u hu t x hx fun z hz hlz => ?_
      rw [hu0 _ (mul_mem_GLs hx hz)]
      refine hoff _ (mul_mem_GLs hx hz) ?_
      rintro ⟨-, hbig⟩
      have hbig' : A < lg (x * z) := hbig
      have h0 := hsub x hx z hz
      have h1 : c₀ * (1 + |t|) ≤ max c₀ 0 * (1 + |t|) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      have h2 : max c₀ 0 * (1 + |t|) ≤ max c₀ 0 * (1 + T) :=
        mul_le_mul_of_nonneg_left (by linarith) hM0
      have h3 : lg (1 : Mat n) + 1 ≤ (lg (1 : Mat n) + 1) * (1 + T) := by nlinarith
      have h4 : A = max c₀ 0 * (1 + T) + (lg (1 : Mat n) + 1) * (1 + T) := by rw [hA]; ring
      linarith
    have hF : (fun x' => ∫ t, (g t : ℂ) • u t x') =ᶠ[𝓝 (1 : Mat n)] 0 := by
      have hN : GLs n ∩ lg ⁻¹' Set.Iio (lg (1 : Mat n) + 1) ∈ 𝓝 (1 : Mat n) :=
        (hsm.continuousOn.isOpen_inter_preimage hGo isOpen_Iio).mem_nhds
          ⟨one_mem_GLs n, Set.mem_preimage.2 (Set.mem_Iio.2 (lt_add_one _))⟩
      filter_upwards [hN] with x hx
      have h0 : ∀ t, (g t : ℂ) • u t x = 0 := by
        intro t
        by_cases ht : |t| ≤ T
        · rw [hzero x hx.1 hx.2 t ht, smul_zero]
        · rw [hg.2.2 t (not_le.1 ht)]
          simp
      simp [h0]
    rw [hact, hk.2.2.2 u hu 1 (one_mem_GLs n)]
    exact (zOp_germ w hF).self_of_nhds

theorem asmKerEx : AsmKerEx := by
  intro hL _ hS hE hU hO n
  obtain ⟨c₀, hc⟩ := hS n
  refine ⟨max c₀ 0 + lg (1 : Mat n) + 1, ?_⟩
  intro _ _ μ _ E
  refine ⟨fun w g T hg => hO n μ E w g T hg, ?_⟩
  rintro k val T hT ⟨m, c, w, g, ks, hi, hsum, -⟩ y hy hlt
  rw [hsum y hy]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [ker_support hL hE hU μ E c₀ hc hT (hi i).1 (hi i).2 hy hlt, smul_zero]

end GlobalTheory.CompanionTheory.WaveKer
