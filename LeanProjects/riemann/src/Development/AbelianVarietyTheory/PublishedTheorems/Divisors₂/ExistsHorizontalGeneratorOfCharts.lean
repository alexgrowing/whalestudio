import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology

namespace GlobalTheory.Published.LogLine

variable {n : ℕ}

def offDivisor (U : Set (Fin n → ℂ)) (S : Finset (Fin n)) : Set (Fin n → ℂ) :=
  {z | z ∈ U ∧ ∀ i ∈ S, z i ≠ 0}

def logPartial (S : Finset (Fin n)) (i : Fin n) (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ :=
  (if i ∈ S then z i else 1) * fderiv ℂ f z (Pi.single i 1)

def IsHorizontalOn (S : Finset (Fin n)) (a : Fin n → (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) → ℂ)
    (V : Set (Fin n → ℂ)) : Prop :=
  DifferentiableOn ℂ f V ∧ ∀ z ∈ V, ∀ i, logPartial S i f z + a i z * f z = 0

end GlobalTheory.Published.LogLine

namespace GlobalTheory.Published

open LogLine

def CanonicalExtensionRankOne : Prop :=
  ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (S : Finset (Fin n)) (a : Fin n → (Fin n → ℂ) → ℂ)
    (f : (Fin n → ℂ) → ℂ), IsOpen U →
    (∀ i, DifferentiableOn ℂ (a i) U) →
    (∀ i ∈ S, ∀ z ∈ U, z i = 0 → a i z = 0) →
    IsHorizontalOn S a f (offDivisor U S) →
    (∀ z ∈ offDivisor U S, f z ≠ 0) →
    ∃ F : (Fin n → ℂ) → ℂ, EqOn F f (offDivisor U S) ∧ IsHorizontalOn S a F U ∧
      (∀ z ∈ U, F z ≠ 0) ∧
      ∀ G : (Fin n → ℂ) → ℂ, ContinuousOn G U → EqOn G f (offDivisor U S) → EqOn G F U

end GlobalTheory.Published

namespace GlobalTheory.Published.LogLine

variable {n : ℕ}

theorem offDivisor_subset (U : Set (Fin n → ℂ)) (S : Finset (Fin n)) : offDivisor U S ⊆ U :=
  fun _ h => h.1

theorem offDivisor_mono {U V : Set (Fin n → ℂ)} (h : U ⊆ V) (S : Finset (Fin n)) :
    offDivisor U S ⊆ offDivisor V S := fun _ hz => ⟨h hz.1, hz.2⟩

theorem isOpen_offDivisor {U : Set (Fin n → ℂ)} (hU : IsOpen U) (S : Finset (Fin n)) :
    IsOpen (offDivisor U S) := by
  have : offDivisor U S = U ∩ ⋂ i ∈ S, {z | z i ≠ 0} := by
    ext z; simp [offDivisor]
  rw [this]
  exact hU.inter (isOpen_biInter_finset fun i _ => isOpen_ne_fun (continuous_apply i) continuous_const)

theorem subset_closure_offDivisor {U : Set (Fin n → ℂ)} (hU : IsOpen U) (S : Finset (Fin n)) :
    U ⊆ closure (offDivisor U S) := by
  have hd : Dense (Set.pi univ fun _ : Fin n => ({0}ᶜ : Set ℂ)) :=
    dense_pi univ fun _ _ => dense_compl_singleton 0
  refine (hd.open_subset_closure_inter hU).trans (closure_mono ?_)
  rintro z ⟨hz, hz'⟩
  exact ⟨hz, fun i _ => hz' i (mem_univ i)⟩

theorem eqOn_of_eqOn_offDivisor {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (S : Finset (Fin n)) {F G : (Fin n → ℂ) → Y}
    (hF : ContinuousOn F U) (hG : ContinuousOn G U) (h : EqOn F G (offDivisor U S)) :
    EqOn F G U :=
  h.of_subset_closure hF hG (offDivisor_subset U S) (subset_closure_offDivisor hU S)

theorem isPreconnected_ball_diff (c p : ℂ) {r : ℝ} (hr : 0 < r) :
    IsPreconnected (ball c r \ {p}) := by
  set e := OpenPartialHomeomorph.univBall c r with he
  have hs : e.source = univ := OpenPartialHomeomorph.univBall_source c r
  have ht : e.target = ball c r := OpenPartialHomeomorph.univBall_target c hr
  have hinj : Function.Injective e := by
    rw [← injOn_univ, ← hs]; exact e.injOn
  have hc : (e ⁻¹' {p}).Countable := (countable_singleton p).preimage hinj
  have h1 := (hc.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected.image e
    (OpenPartialHomeomorph.continuous_univBall c r).continuousOn
  have h2 : e '' (e ⁻¹' {p})ᶜ = ball c r \ {p} := by
    rw [← preimage_compl, image_preimage_eq_inter_range, ← image_univ, ← hs,
      e.image_source_eq_target, ht, inter_comm]
    rfl
  rwa [h2] at h1

theorem isPreconnected_offDivisor_ball (c : Fin n → ℂ) {r : ℝ} (hr : 0 < r) (S : Finset (Fin n)) :
    IsPreconnected (offDivisor (ball c r) S) := by
  have : offDivisor (ball c r) S =
      Set.pi univ fun i => if i ∈ S then ball (c i) r \ {0} else ball (c i) r := by
    ext z
    simp only [offDivisor, ball_pi c hr, mem_setOf_eq, Set.mem_pi, mem_univ, true_imp_iff]
    constructor
    · rintro ⟨h1, h2⟩ i
      split_ifs with hi
      · exact ⟨h1 i, h2 i hi⟩
      · exact h1 i
    · intro h
      refine ⟨fun i => ?_, fun i hi => ?_⟩
      · have := h i
        split_ifs at this
        · exact this.1
        · exact this
      · have := h i
        rw [if_pos hi] at this
        exact this.2
  rw [this]
  refine isPreconnected_univ_pi fun i => ?_
  split_ifs
  · exact isPreconnected_ball_diff _ _ hr
  · exact (convex_ball _ _).isPreconnected

theorem exists_div_ball {a : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r : ℝ} {i : Fin n} (hc : c i = 0)
    (ha : DifferentiableOn ℂ a (ball c r)) (h0 : ∀ z ∈ ball c r, z i = 0 → a z = 0) :
    ∃ b : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ b (ball c r) ∧ ∀ z ∈ ball c r, a z = z i * b z := by
  set p : ℝ → (Fin n → ℂ) → (Fin n → ℂ) :=
    fun t z => z + (((t : ℂ) - 1) * z i) • (Pi.single i 1 : Fin n → ℂ) with hp
  have hmem : ∀ t ∈ Set.uIcc (0 : ℝ) 1, ∀ z ∈ ball c r, p t z ∈ ball c r := by
    intro t ht z hz
    have hr := pos_of_mem_ball hz
    rw [uIcc_of_le zero_le_one] at ht
    rw [ball_pi c hr] at hz ⊢
    intro j _
    have hj := hz j (mem_univ j)
    by_cases hji : j = i
    · subst hji
      rw [mem_ball_iff_norm, hc, sub_zero] at hj ⊢
      have : p t z j = t * z j := by simp [hp]; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ht.2) hj
    · have : p t z j = z j := by simp [hp, hji]
      rwa [this]
  have hd := GlobalTheory.SCV.differentiableOn_fderiv_apply isOpen_ball ha (Pi.single i 1)
  have key := GlobalTheory.differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
    (F := fun t z => fderiv ℂ a (p t z) (Pi.single i 1)) (U := ball c r) isOpen_ball
    (a := 0) (b := 1) ?_ ?_
  · refine ⟨_, key.1, fun z hz => ?_⟩
    have hder : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => a (p s z))
        (z i * fderiv ℂ a (p t z) (Pi.single i 1)) t := by
      intro t ht
      have h1 : HasFDerivAt a (fderiv ℂ a (p t z)) (p t z) :=
        (ha.differentiableAt (isOpen_ball.mem_nhds (hmem t ht z hz))).hasFDerivAt
      have h2 : HasDerivAt (fun w : ℂ => z + ((w - 1) * z i) • (Pi.single i 1 : Fin n → ℂ))
          ((z i) • (Pi.single i 1 : Fin n → ℂ)) (t : ℂ) := by
        simpa using ((((hasDerivAt_id (t : ℂ)).sub_const 1).mul_const (z i)).smul_const
          (Pi.single i 1 : Fin n → ℂ)).const_add z
      have h3 := (h1.comp_hasDerivAt (t : ℂ) h2).comp_ofReal
      simpa [hp, Function.comp_def] using h3
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      (((key.2 z hz).1).const_mul (z i))
    rw [intervalIntegral.integral_const_mul] at hint
    rw [hint, h0 (p 0 z) (hmem 0 left_mem_uIcc z hz) (by simp [hp])]
    simp [hp]
  · refine hd.continuousOn.comp (f := fun q : ℝ × (Fin n → ℂ) => p q.1 q.2) ?_
      fun q hq => hmem _ hq.1 _ hq.2
    simp only [hp]
    fun_prop
  · intro t ht
    refine hd.comp (f := p t) ?_ fun z hz => hmem t ht z hz
    simp only [hp]
    fun_prop

theorem exists_ball_div {U : Set (Fin n → ℂ)} (hU : IsOpen U) (S : Finset (Fin n))
    {a : Fin n → (Fin n → ℂ) → ℂ} (ha : ∀ i, DifferentiableOn ℂ (a i) U)
    (h0 : ∀ i ∈ S, ∀ z ∈ U, z i = 0 → a i z = 0) {c : Fin n → ℂ} (hc : c ∈ U) :
    ∃ r > 0, ball c r ⊆ U ∧ ∃ b : Fin n → (Fin n → ℂ) → ℂ,
      (∀ i, DifferentiableOn ℂ (b i) (ball c r)) ∧
      ∀ i, ∀ z ∈ ball c r, a i z = (if i ∈ S then z i else 1) * b i z := by
  have hev : ∀ᶠ z in 𝓝 c, z ∈ U ∧ ∀ i, c i ≠ 0 → z i ≠ 0 := by
    refine Filter.Eventually.and (hU.mem_nhds hc) (eventually_all.mpr fun i => ?_)
    by_cases h : c i = 0
    · simp [h]
    · exact ((continuous_apply i).continuousAt.eventually_ne h).mono fun z hz _ => hz
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hsub : ball c r ⊆ U := fun z hz => (h z hz).1
  refine ⟨r, hr, hsub, ?_⟩
  have : ∀ i, ∃ b : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ b (ball c r) ∧
      ∀ z ∈ ball c r, a i z = (if i ∈ S then z i else 1) * b z := by
    intro i
    by_cases hi : i ∈ S
    · simp only [if_pos hi]
      by_cases hci : c i = 0
      · exact exists_div_ball hci ((ha i).mono hsub) fun z hz => h0 i hi z (hsub hz)
      · refine ⟨fun z => a i z * (z i)⁻¹, ((ha i).mono hsub).mul
          (DifferentiableOn.fun_inv (𝕜 := ℂ) (h := fun z : Fin n → ℂ => z i) (by fun_prop)
            fun z hz => (h z hz).2 i hci), fun z hz => ?_⟩
        have := (h z hz).2 i hci
        field_simp
    · exact ⟨a i, (ha i).mono hsub, fun z _ => by simp [hi]⟩
  choose b hb using this
  exact ⟨b, fun i => (hb i).1, fun i => (hb i).2⟩

def oneForm (b : Fin n → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : (Fin n → ℂ) →L[ℂ] ℂ :=
  ∑ i, b i z • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i

theorem oneForm_single (b : Fin n → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) (i : Fin n) :
    oneForm b z (Pi.single i 1) = b i z := by
  simp [oneForm, Pi.single_apply]

theorem clm_ext_single {L M : (Fin n → ℂ) →L[ℂ] ℂ}
    (h : ∀ i, L (Pi.single i 1) = M (Pi.single i 1)) : L = M := by
  ext v
  rw [← Finset.univ_sum_single v, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (v i) : Fin n → ℂ) = v i • (Pi.single i 1 : Fin n → ℂ) := by
    rw [← Pi.single_smul]; simp
  rw [this, map_smul, map_smul, h i]

theorem fderiv_symm_of_fderiv_eq {V : Set (Fin n → ℂ)} (hV : IsOpen V)
    {β : (Fin n → ℂ) → (Fin n → ℂ) →L[ℂ] ℂ} {f : (Fin n → ℂ) → ℂ}
    (hβ : DifferentiableOn ℂ β V) (hf : DifferentiableOn ℂ f V) (hne : ∀ z ∈ V, f z ≠ 0)
    (h : ∀ z ∈ V, fderiv ℂ f z = -(f z • β z)) {z : Fin n → ℂ} (hz : z ∈ V) (x y : Fin n → ℂ) :
    fderiv ℂ β z x y = fderiv ℂ β z y x := by
  have hn := hV.mem_nhds hz
  have hs : IsSymmSndFDerivAt ℂ f z :=
    (GlobalTheory.SCV.contDiffAt_of_differentiableOn hf hn 2).isSymmSndFDerivAt (by simp)
  have he : fderiv ℂ f =ᶠ[𝓝 z] fun w => -(f w • β w) := by
    filter_upwards [hn] with w hw using h w hw
  have h1 := ((hf.differentiableAt hn).hasFDerivAt.smul (hβ.differentiableAt hn).hasFDerivAt).neg
  have h2 : fderiv ℂ (fderiv ℂ f) z = _ := he.fderiv_eq.trans h1.fderiv
  have h3 := hs x y
  rw [h2, h z hz] at h3
  simp at h3
  have := hne z hz
  apply mul_left_cancel₀ this
  linear_combination -h3

theorem exists_local_extension {c : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (S : Finset (Fin n))
    {b : Fin n → (Fin n → ℂ) → ℂ} (hb : ∀ i, DifferentiableOn ℂ (b i) (ball c r))
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (offDivisor (ball c r) S))
    (hne : ∀ z ∈ offDivisor (ball c r) S, f z ≠ 0)
    (h : ∀ z ∈ offDivisor (ball c r) S, ∀ i, fderiv ℂ f z (Pi.single i 1) = -(f z * b i z)) :
    ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (ball c r) ∧
      EqOn F f (offDivisor (ball c r) S) ∧ ∀ z ∈ ball c r, F z ≠ 0 := by
  set V := offDivisor (ball c r) S with hV
  have hVo : IsOpen V := isOpen_offDivisor isOpen_ball S
  have hVs : V ⊆ ball c r := offDivisor_subset _ _
  have hβ : DifferentiableOn ℂ (oneForm b) (ball c r) :=
    DifferentiableOn.fun_sum fun i _ => (hb i).smul_const _
  have hfd : ∀ z ∈ V, fderiv ℂ f z = -(f z • oneForm b z) := fun z hz =>
    clm_ext_single fun i => by simp [h z hz i, oneForm_single]
  have hc := (GlobalTheory.SCV.differentiableOn_fderiv isOpen_ball hβ).continuousOn
  have hsym : ∀ x y, EqOn (fun z => fderiv ℂ (oneForm b) z x y)
      (fun z => fderiv ℂ (oneForm b) z y x) (ball c r) := fun x y =>
    eqOn_of_eqOn_offDivisor isOpen_ball S
      ((hc.clm_apply continuousOn_const).clm_apply continuousOn_const)
      ((hc.clm_apply continuousOn_const).clm_apply continuousOn_const)
      fun z hz => fderiv_symm_of_fderiv_eq hVo (hβ.mono hVs) hf hne hfd hz x y
  obtain ⟨g, hg⟩ := (convex_ball c r).exists_forall_hasFDerivAt_of_fderiv_symmetric (𝕜 := ℂ)
    (ω := oneForm b) isOpen_ball (hβ.restrictScalars ℝ) fun z hz x y => by
      rw [(hβ.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
      exact hsym x y hz
  have hprod : ∀ z ∈ V, HasFDerivAt (fun w => f w * Complex.exp (g w))
      (0 : (Fin n → ℂ) →L[ℂ] ℂ) z := by
    intro z hz
    have h1 := ((hf.differentiableAt (hVo.mem_nhds hz)).hasFDerivAt).mul (hg z (hVs hz)).cexp
    refine h1.congr_fderiv ?_
    rw [hfd z hz]
    ext v
    simp
    ring
  obtain ⟨k, hk⟩ := hVo.exists_is_const_of_fderiv_eq_zero (𝕜 := ℂ)
    (isPreconnected_offDivisor_ball c hr S)
    (fun z hz => (hprod z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hprod z hz).fderiv)
  obtain ⟨z₀, hz₀⟩ : V.Nonempty :=
    closure_nonempty_iff.mp ⟨c, subset_closure_offDivisor isOpen_ball S (mem_ball_self hr)⟩
  have hk0 : k ≠ 0 := hk z₀ hz₀ ▸ mul_ne_zero (hne z₀ hz₀) (Complex.exp_ne_zero _)
  refine ⟨fun z => k * Complex.exp (-g z), fun z hz => ?_, fun z hz => ?_,
    fun z _ => mul_ne_zero hk0 (Complex.exp_ne_zero _)⟩
  · exact (((hg z hz).neg.cexp).const_mul k).differentiableAt.differentiableWithinAt
  · simp only
    rw [← hk z hz, mul_assoc, ← Complex.exp_add]
    simp

theorem continuousOn_logPartial {U : Set (Fin n → ℂ)} (hU : IsOpen U) (S : Finset (Fin n))
    (i : Fin n) {F : (Fin n → ℂ) → ℂ} (hF : DifferentiableOn ℂ F U) :
    ContinuousOn (logPartial S i F) U := by
  refine ContinuousOn.mul ?_ (GlobalTheory.SCV.differentiableOn_fderiv_apply hU hF _).continuousOn
  split_ifs <;> fun_prop

end GlobalTheory.Published.LogLine

namespace GlobalTheory.Published

open LogLine

theorem canonicalExtensionRankOne_holds : CanonicalExtensionRankOne := by
  intro n U S a f hU ha h0 hf hne
  set V := offDivisor U S with hV
  have hVo : IsOpen V := isOpen_offDivisor hU S
  have hloc : ∀ c ∈ U, ∃ G : (Fin n → ℂ) → ℂ, DifferentiableAt ℂ G c ∧ G c ≠ 0 ∧
      extendFrom V f =ᶠ[𝓝 c] G ∧ (c ∈ V → G c = f c) := by
    intro c hc
    obtain ⟨r, hr, hsub, b, hb, hab⟩ := exists_ball_div hU S ha h0 hc
    have hm := offDivisor_mono hsub S
    obtain ⟨G, hG, hGf, hG0⟩ := exists_local_extension hr S hb (hf.1.mono hm)
      (fun z hz => hne z (hm hz)) fun z hz i => by
        have h1 := hf.2 z (hm hz) i
        have h2 : (if i ∈ S then z i else 1) ≠ 0 := by
          split_ifs with hi
          · exact hz.2 i hi
          · exact one_ne_zero
        rw [logPartial, hab i z hz.1] at h1
        apply mul_left_cancel₀ h2
        linear_combination h1
    refine ⟨G, hG.differentiableAt (ball_mem_nhds c hr), hG0 c (mem_ball_self hr), ?_,
      fun hcV => hGf ⟨mem_ball_self hr, hcV.2⟩⟩
    filter_upwards [ball_mem_nhds c hr] with z hz
    refine extendFrom_eq (subset_closure_offDivisor hU S (hsub hz)) ?_
    have hn := isOpen_ball.mem_nhds hz
    refine ((hG.differentiableAt hn).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [nhdsWithin_le_nhds hn, self_mem_nhdsWithin] with w hw hwV
    exact hGf ⟨hw, hwV.2⟩
  have hFd : DifferentiableOn ℂ (extendFrom V f) U := fun c hc => by
    obtain ⟨G, hG, -, he, -⟩ := hloc c hc
    exact (hG.congr_of_eventuallyEq he).differentiableWithinAt
  have hFf : EqOn (extendFrom V f) f V := fun c hc => by
    obtain ⟨G, -, -, he, h⟩ := hloc c hc.1
    rw [he.eq_of_nhds, h hc]
  refine ⟨extendFrom V f, hFf, ⟨hFd, fun z hz i => ?_⟩, fun c hc => ?_, fun G hG hGf =>
    eqOn_of_eqOn_offDivisor hU S hG hFd.continuousOn (hGf.trans hFf.symm)⟩
  · refine eqOn_of_eqOn_offDivisor (G := fun _ => 0) hU S
      (F := fun z => logPartial S i (extendFrom V f) z + a i z * extendFrom V f z)
      ((continuousOn_logPartial hU S i hFd).add ((ha i).continuousOn.mul hFd.continuousOn))
      continuousOn_const (fun w hw => ?_) hz
    have he : extendFrom V f =ᶠ[𝓝 w] f := hFf.eventuallyEq_of_mem (hVo.mem_nhds hw)
    have := hf.2 w hw i
    simp only [logPartial] at this ⊢
    rw [he.fderiv_eq, hFf hw, this]
  · obtain ⟨G, -, hG0, he, -⟩ := hloc c hc
    rwa [he.eq_of_nhds]

end GlobalTheory.Published

namespace GlobalTheory.Published

open LogLine

end GlobalTheory.Published

namespace GlobalTheory.Published.LogLine

end GlobalTheory.Published.LogLine
