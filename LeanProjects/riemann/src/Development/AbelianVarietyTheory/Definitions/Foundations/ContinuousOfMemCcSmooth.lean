import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.SplitWeil
open scoped ENNReal NNReal Topology Pointwise ComplexConjugate ContDiff InnerProductSpace

noncomputable section

namespace GlobalTheory.Orb

section Conv

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {f f' f'' : G → ℂ}

theorem indicator_mem_SB {X : Type*} [TopologicalSpace X] [T2Space X] {U : Set X} (ho : IsOpen U)
    (hc : IsCompact U) : U.indicator (1 : X → ℂ) ∈ SB X := by
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun g => ?_, .intro hc fun x hx => indicator_of_notMem hx _⟩
  by_cases hg : g ∈ U
  · exact ⟨U, ho, hg, fun x hx => by simp [hx, hg]⟩
  · exact ⟨Uᶜ, hc.isClosed.isOpen_compl, hg, fun x hx => by rw [indicator_of_notMem hx, indicator_of_notMem hg]⟩

theorem comp_mem_SB {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {φ : Y → ℂ} (h : φ ∈ SB Y) (e : X ≃ₜ Y) :
    φ ∘ e ∈ SB X := ⟨h.1.comp_continuous e.continuous, h.2.comp_homeomorph e⟩

theorem starFn_mem_SB (h : f ∈ SB G) : starFn f ∈ SB G :=
  ⟨(h.1.comp_continuous continuous_inv).comp conj, hasCompactSupport_starFn h.2⟩

theorem exists_biinvariant (h : f ∈ SB G) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g, f (k * g) = f g ∧ f (g * k) = f g := by
  refine ⟨leftStabilizer f ⊓ leftStabilizer (starFn f), (isOpen_leftStabilizer h.1 h.2).inter
    (isOpen_leftStabilizer (starFn_mem_SB h).1 (starFn_mem_SB h).2), fun k hk g => ⟨hk.1 g, ?_⟩⟩
  exact (starRingEnd ℂ).injective (by simpa [starFn] using (leftStabilizer (starFn f)).inv_mem hk.2 g⁻¹)

variable [MeasurableSpace G] {μ : Measure G}

omit [IsTopologicalGroup G] in

theorem conv_eq_zero {y : G} (h : y ∉ tsupport f * tsupport f') : conv μ f f' y = 0 := by
  have : ∀ x, f x * f' (x⁻¹ * y) = 0 := fun x => by
    by_contra hne
    exact h ⟨x, subset_tsupport f (left_ne_zero_of_mul hne), _, subset_tsupport f' (right_ne_zero_of_mul hne), by simp⟩
  simp [conv, this]

theorem hasCompactSupport_conv (hc : HasCompactSupport f) (hc' : HasCompactSupport f') :
    HasCompactSupport (conv μ f f') := .intro (IsCompact.mul hc hc') fun _ => conv_eq_zero

theorem conv_mem_SB (h : f ∈ SB G) (h' : f' ∈ SB G) : conv μ f f' ∈ SB G := by
  obtain ⟨U, hU, hf⟩ := exists_biinvariant h'
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(g⁻¹ * ·) ⁻¹' U, hU.preimage (by fun_prop), by simp,
    fun x hx => ?_⟩, hasCompactSupport_conv h.2 h'.2⟩
  refine integral_congr_ae (.of_forall fun z => ?_)
  simpa [mul_assoc] using congrArg (f z * ·) (hf _ hx (z⁻¹ * g)).2

variable [BorelSpace G]

theorem starFn_conv [μ.IsMulLeftInvariant] (f f' : G → ℂ) :
    starFn (conv μ f f') = conv μ (starFn f') (starFn f) := by
  funext y
  rw [starFn, conv, conv, ← integral_conj, ← integral_mul_left_eq_self _ y⁻¹]
  simp [starFn, mul_comm]

variable [IsFiniteMeasureOnCompacts μ]

theorem conv_assoc [μ.IsMulLeftInvariant] (hf : Continuous f) (hc : HasCompactSupport f) (hf' : Continuous f')
    (hc' : HasCompactSupport f') (hf'' : Continuous f'') :
    conv μ (conv μ f f') f'' = conv μ f (conv μ f' f'') := by
  funext z
  have hF : Continuous (Function.uncurry fun x y : G => f x * f' (x⁻¹ * y) * f'' (y⁻¹ * z)) :=
    ((hf.comp continuous_fst).mul (hf'.comp (continuous_fst.inv.mul continuous_snd))).mul
      (hf''.comp (continuous_snd.inv.mul continuous_const))
  have hFc : HasCompactSupport (Function.uncurry fun x y : G => f x * f' (x⁻¹ * y) * f'' (y⁻¹ * z)) := by
    refine .intro (IsCompact.prod hc (IsCompact.mul hc hc')) fun p hp => ?_
    by_contra hne
    have h0 : f p.1 * f' (p.1⁻¹ * p.2) ≠ 0 := left_ne_zero_of_mul hne
    have h1 := subset_tsupport f (left_ne_zero_of_mul h0)
    exact hp ⟨h1, _, h1, _, subset_tsupport f' (right_ne_zero_of_mul h0), by simp⟩
  simp only [conv, ← integral_mul_const, ← integral_const_mul]
  rw [← integral_integral_swap_of_hasCompactSupport hF hFc]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only
  rw [← integral_mul_left_eq_self _ x]
  simp [mul_assoc]

end Conv

section Type_

variable {G Q W : Type} [Group G] [Group Q] [AddCommGroup W] [Module ℂ W] [MeasurableSpace G] (μ : Measure G)
  {K : Subgroup G} (r : K →* Q) (τ : Representation ℂ Q W)

open Classical in

def typeIdem : G → ℂ := fun g =>
  if h : g ∈ K then (Module.finrank ℂ W : ℂ) * (μ.real K : ℂ)⁻¹ * conj (τ.character (r ⟨g, h⟩)) else 0

theorem typeIdem_coe (k : K) :
    typeIdem μ r τ k = (Module.finrank ℂ W : ℂ) * (μ.real K : ℂ)⁻¹ * conj (τ.character (r k)) := dif_pos k.2

theorem typeIdem_of_notMem {g : G} (h : g ∉ K) : typeIdem μ r τ g = 0 := dif_neg h

theorem typeIdem_mul_ker {k : K} (hk : r k = 1) (g : G) :
    typeIdem μ r τ (k * g) = typeIdem μ r τ g ∧ typeIdem μ r τ (g * k) = typeIdem μ r τ g := by
  by_cases h : g ∈ K
  · have h1 := typeIdem_coe μ r τ (k * ⟨g, h⟩)
    have h2 := typeIdem_coe μ r τ (⟨g, h⟩ * k)
    rw [map_mul, hk] at h1 h2
    rw [one_mul] at h1
    rw [mul_one] at h2
    exact ⟨h1.trans (typeIdem_coe μ r τ ⟨g, h⟩).symm, h2.trans (typeIdem_coe μ r τ ⟨g, h⟩).symm⟩
  · rw [typeIdem_of_notMem μ r τ h, typeIdem_of_notMem, typeIdem_of_notMem]
    · exact ⟨rfl, rfl⟩
    · rwa [K.mul_mem_cancel_right k.2]
    · rwa [K.mul_mem_cancel_left k.2]

theorem starFn_typeIdem [Finite Q] [FiniteDimensional ℂ W] : starFn (typeIdem μ r τ) = typeIdem μ r τ := by
  funext g
  by_cases h : g ∈ K
  · have h1 := typeIdem_coe μ r τ (⟨g, h⟩⁻¹)
    have h2 : τ.character (r ⟨g, h⟩)⁻¹ = conj (τ.character (r ⟨g, h⟩)) := by
      have := Fintype.ofFinite Q
      exact GlobalTheory.BadShare.ZCalc.character_inv (FDRep.of τ) _
    rw [map_inv, h2] at h1
    refine (congrArg conj h1).trans (Eq.trans ?_ (typeIdem_coe μ r τ ⟨g, h⟩).symm)
    simp
  · rw [starFn, typeIdem_of_notMem μ r τ h, typeIdem_of_notMem μ r τ (by simpa using h), map_zero]

theorem typeIdem_mem_SB [TopologicalSpace G] [IsTopologicalGroup G] (ho : IsOpen (K : Set G))
    (hc : IsCompact (K : Set G)) (hr : IsOpen (r.ker : Set K)) : typeIdem μ r τ ∈ SB G := by
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(g⁻¹ * ·) ⁻¹' ((↑) '' (r.ker : Set K)),
    (ho.isOpenMap_subtype_val _ hr).preimage (by fun_prop), ⟨1, one_mem _, by simp⟩, ?_⟩,
    .intro hc fun x => typeIdem_of_notMem μ r τ⟩
  rintro x ⟨k, hk, e⟩
  rw [← (typeIdem_mul_ker μ r τ hk g).2, e, mul_inv_cancel_left]

example : typeIdem μ r (Representation.trivial ℂ Q ℂ) = (μ.real K : ℂ)⁻¹ • (K : Set G).indicator 1 := by
  funext g
  by_cases h : g ∈ K
  · rw [typeIdem_coe μ r _ ⟨g, h⟩]
    simp [Representation.character, h]
  · simp [typeIdem_of_notMem μ r _ h, h]

end Type_

section Smooth

variable {H X : Type*} [TopologicalSpace H] [NormedAddCommGroup X] [NormedSpace ℝ X]

def CcSmooth (c : H → X) : Submodule ℂ (H → ℂ) where
  carrier := {f | HasCompactSupport f ∧ ∃ Φ : X → ℂ, ContDiff ℝ ∞ Φ ∧ ∀ g, f g = Φ (c g)}
  zero_mem' := ⟨HasCompactSupport.zero, 0, contDiff_const, fun _ => rfl⟩
  add_mem' := by
    rintro f f' ⟨h, Φ, hΦ, e⟩ ⟨h', Φ', hΦ', e'⟩
    exact ⟨h.add h', Φ + Φ', hΦ.add hΦ', fun g => by simp [e, e']⟩
  smul_mem' := by
    rintro a f ⟨h, Φ, hΦ, e⟩
    exact ⟨h.smul_left (f := fun _ => a), a • Φ, hΦ.const_smul a, fun g => by simp [e]⟩

variable {c : H → X} {f : H → ℂ}

theorem mem_ccSmooth : f ∈ CcSmooth c ↔ HasCompactSupport f ∧ ∃ Φ : X → ℂ, ContDiff ℝ ∞ Φ ∧ ∀ g, f g = Φ (c g) :=
  Iff.rfl

theorem continuous_of_mem_ccSmooth (hc : Continuous c) (h : f ∈ CcSmooth c) : Continuous f := by
  obtain ⟨-, Φ, hΦ, e⟩ := h
  exact (hΦ.continuous.comp hc).congr fun g => (e g).symm

theorem ccSmooth_le {X' : Type*} [NormedAddCommGroup X'] [NormedSpace ℝ X'] {c' : H → X'} {p : X' → X}
    (hp : ContDiff ℝ ∞ p) (e : ∀ g, c g = p (c' g)) : CcSmooth c ≤ CcSmooth c' := by
  rintro f ⟨h, Φ, hΦ, e'⟩
  exact ⟨h, Φ ∘ p, hΦ.comp hp, fun g => by simp [e, e']⟩

theorem exists_bump [LocallyCompactSpace H] [T2Space H] [FiniteDimensional ℝ X] (hc : Topology.IsInducing c) {g : H}
    {U : Set H} (hU : U ∈ 𝓝 g) : ∃ φ : H → ℝ, (fun x => (φ x : ℂ)) ∈ CcSmooth c ∧ φ g = 1 ∧ (∀ x, φ x ∈ Icc 0 1) ∧
      tsupport φ ⊆ U := by
  obtain ⟨C, hC, hCU, hCc⟩ := local_compact_nhds hU
  rw [hc.nhds_eq_comap] at hC
  obtain ⟨s, hs, hsC⟩ := hC
  obtain ⟨Φ, h1, -, h3, h4, h5⟩ := exists_contDiff_tsupport_subset (n := ⊤) hs
  have h0 : ∀ x ∉ C, Φ (c x) = 0 := fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hsC (h1 h))
  exact ⟨fun x => Φ (c x), ⟨.intro hCc fun x hx => by simp [h0 x hx], fun y => Φ y,
    Complex.ofRealCLM.contDiff.comp h3, fun _ => rfl⟩, h5, fun x => h4 ⟨_, rfl⟩,
    (closure_minimal (Function.support_subset_iff'.2 h0) hCc.isClosed).trans hCU⟩

end Smooth

def IsRegSS {A n : Type*} [CommRing A] [Fintype n] [DecidableEq n] (M : Matrix n n A) : Prop := M.charpoly.Separable

section Real

variable {H n : Type} [Group H] [TopologicalSpace H] [Fintype n] [DecidableEq n]
  {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def matCoord (ι : H →* Matrix n n ℂ) (g : H) : n → n → ℂ := fun i j => ι g i j

abbrev CcMat (ι : H →* Matrix n n ℂ) : Submodule ℂ (H → ℂ) := CcSmooth (matCoord ι)

def IsBiFinite (K : Subgroup H) (f : H → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => f (k * g * k')})

def IsUnitEquiv (π : H →* (V →L[ℂ] V)) (π' : H →* (W →L[ℂ] W)) : Prop :=
  ∃ A : V ≃ₗᵢ[ℂ] W, ∀ g v, A (π g v) = π' g (A v)

variable [MeasurableSpace H]

def IsTempered (μ : Measure H) (π : H →* (V →L[ℂ] V)) : Prop :=
  ∃ v : V, v ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → Integrable (fun g => ‖⟪v, π g v⟫_ℂ‖ ^ (2 + ε)) μ

variable [CompleteSpace V] [CompleteSpace W]

def IsCharFn (ι : H →* Matrix n n ℂ) (μ : Measure H) (π : H →* (V →L[ℂ] V)) (Θ : H → ℂ) : Prop :=
  LocallyIntegrable Θ μ ∧ (∀ s, IsRegSS (ι s) → ContinuousAt Θ s) ∧
    ∀ f ∈ CcMat ι, HasTrace (repOp π μ f) (∫ g, f g * Θ g ∂μ)

structure IsPseudoCoeff (ι : H →* Matrix n n ℂ) (μ : Measure H) (D : H →* (V →L[ℂ] V)) (f : H → ℂ) : Prop where

  mem : f ∈ CcMat ι

  trace_self : HasTrace (repOp D μ f) 1

  trace_other : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    (π : H →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → IsTempered μ π → ¬ IsUnitEquiv π D →
      HasTrace (repOp π μ f) 0

  orb_noncompact : ∀ s, IsRegSS (ι s) → ¬ IsCompact (cent s : Set H) →
    ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant], HasOrbInt μ s dt f 0

  orb_compact : ∃ Θ, IsCharFn ι μ D Θ ∧ ∀ s, IsRegSS (ι s) → IsCompact (cent s : Set H) →
    ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant],
      HasOrbInt μ s dt f (conj (Θ s) / dt.real univ)

variable {ι : H →* Matrix n n ℂ} {μ : Measure H} {π : H →* (V →L[ℂ] V)} [BorelSpace H]

omit [CompleteSpace V] in

theorem isTempered_of_memLp_two (hπ : IsUnitaryRep π) {v : V} (hv : v ≠ 0)
    (h : MemLp (fun g => ⟪v, π g v⟫_ℂ) 2 μ) : IsTempered μ π := by
  refine ⟨v, hv, fun ε hε => ?_⟩
  have h2 := ((memLp_two_iff_integrable_sq_norm h.1).1 h).mul_const ((‖v‖ * ‖v‖) ^ ε)
  refine h2.mono' ((h.1.norm.aemeasurable.pow_const _).aestronglyMeasurable) (.of_forall fun g => ?_)
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_add' (norm_nonneg _) (by positivity), Real.rpow_two]
  gcongr
  simpa [hπ.norm_apply] using norm_inner_le_norm (𝕜 := ℂ) v (π g v)

omit [CompleteSpace V] in

theorem isTempered_of_finite [IsFiniteMeasure μ] [SecondCountableTopology H] [Nontrivial V] (hπ : IsUnitaryRep π) :
    IsTempered μ π := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine isTempered_of_memLp_two hπ hv (MemLp.of_bound
    (continuous_const.inner (hπ.continuous_apply v)).aestronglyMeasurable (‖v‖ * ‖v‖) (.of_forall fun g => ?_))
  simpa [hπ.norm_apply] using norm_inner_le_norm (𝕜 := ℂ) v (π g v)

theorem IsCharFn.unique [LocallyCompactSpace H] [T2Space H] [μ.IsOpenPosMeasure]
    (hι : Topology.IsInducing (matCoord ι)) {Θ Θ' : H → ℂ} (h : IsCharFn ι μ π Θ) (h' : IsCharFn ι μ π Θ') {s : H}
    (hs : IsRegSS (ι s)) : Θ s = Θ' s := by
  by_contra hne
  set a := Θ s - Θ' s
  have ha : 0 < (conj a * a).re := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_pos.2 (sub_ne_zero.2 hne)
  have hc : ContinuousAt (fun x => (conj a * (Θ x - Θ' x)).re) s :=
    Complex.continuous_re.continuousAt.comp (continuousAt_const.mul ((h.2.1 s hs).sub (h'.2.1 s hs)))
  obtain ⟨φ, hφ, h1, h01, hU⟩ := exists_bump hι (hc.eventually (lt_mem_nhds ha))
  have hφc := continuous_of_mem_ccSmooth hι.continuous hφ
  have hi : ∀ {Ξ : H → ℂ}, LocallyIntegrable Ξ μ → Integrable (fun g => (φ g : ℂ) * Ξ g) μ := fun hΞ =>
    hΞ.integrable_smul_left_of_hasCompactSupport hφc hφ.1
  have hI : Integrable (fun g => conj a * ((φ g : ℂ) * Θ g - φ g * Θ' g)) μ :=
    ((hi h.1).sub (hi h'.1)).const_mul (conj a)
  have e : ∀ g, RCLike.re (conj a * ((φ g : ℂ) * Θ g - φ g * Θ' g)) = φ g * (conj a * (Θ g - Θ' g)).re := fun g => by
    rw [← mul_sub, mul_left_comm, ← Complex.re_ofReal_mul]; rfl
  have h0 : ∫ g, φ g * (conj a * (Θ g - Θ' g)).re ∂μ = 0 := by
    simp only [← e]
    rw [integral_re hI, integral_const_mul, integral_sub (hi h.1) (hi h'.1), ← (h.2.2 _ hφ).2, ← (h'.2.2 _ hφ).2]
    simp
  have hnn : 0 ≤ fun g => φ g * (conj a * (Θ g - Θ' g)).re := fun g => by
    by_cases hg : φ g = 0
    · simp [hg]
    · exact mul_nonneg (h01 g).1 (hU (subset_tsupport _ hg)).le
  have hφr : Continuous φ := Complex.continuous_re.comp hφc
  refine ((integral_pos_iff_support_of_nonneg hnn (by simpa only [← e] using hI.re)).2 ?_).ne' h0
  refine Measure.measure_pos_of_mem_nhds μ ((hφr.continuousAt.mul hc).eventually_ne ?_)
  exact mul_ne_zero (h1 ▸ one_ne_zero) ha.ne'

theorem IsPseudoCoeff.orb_of_isCharFn [LocallyCompactSpace H] [T2Space H] [μ.IsOpenPosMeasure] {f : H → ℂ}
    (h : IsPseudoCoeff ι μ π f) (hι : Topology.IsInducing (matCoord ι)) {Θ : H → ℂ} (hΘ : IsCharFn ι μ π Θ) {s : H}
    (hs : IsRegSS (ι s)) (hT : IsCompact (cent s : Set H)) (dt : Measure (cent s)) [dt.IsHaarMeasure]
    [dt.IsMulRightInvariant] : HasOrbInt μ s dt f (conj (Θ s) / dt.real univ) := by
  obtain ⟨Θ', h1, h2⟩ := h.orb_compact
  rw [hΘ.unique hι h1 hs]
  exact h2 s hs hT dt

theorem isPseudoCoeff_char [IsTopologicalGroup H] [CompactSpace H] [T2Space H] [SecondCountableTopology H]
    [μ.IsHaarMeasure] (hι : Continuous (matCoord ι)) {χ : H →* Circle} (hχ : (fun g => conj (χ g : ℂ)) ∈ CcMat ι) :
    IsPseudoCoeff ι μ (charRep χ) fun g => conj (χ g : ℂ) / μ.real univ := by
  have h0 : (μ.real univ : ℂ) ≠ 0 := by
    exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨(isOpen_univ.measure_pos μ univ_nonempty).ne', measure_ne_top _ _⟩
  have hc := continuous_of_mem_ccSmooth hι hχ
  have hc' : Continuous fun g => (χ g : ℂ) := (Complex.continuous_conj.comp hc).congr fun g => by simp
  have hχc : Continuous χ := continuous_induced_rng.2 hc'
  have hf : Continuous fun g => conj (χ g : ℂ) / μ.real univ := hc.div_const _
  have hs : ∀ φ : H → ℂ, HasCompactSupport φ := fun φ => (isClosed_tsupport φ).isCompact
  have hn : ∀ z : Circle, conj (z : ℂ) * z = 1 := fun z => by
    rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  refine ⟨?_, ?_, fun U _ _ _ π hπ hirr _ hne => ?_, fun s _ hT => absurd (isClosed_cent s).isCompact hT,
    fun g => χ g, ⟨hc'.locallyIntegrable, fun s _ => hc'.continuousAt, fun f hf' =>
      repTrace_charRep hχc (continuous_of_mem_ccSmooth hι hf') hf'.1⟩, fun s _ hT dt _ _ => ?_⟩
  · simp only [div_eq_inv_mul]
    exact (CcMat ι).smul_mem (μ.real univ : ℂ)⁻¹ hχ
  · convert repTrace_charRep (μ := μ) hχc hf (hs _) using 1
    simp [div_mul_eq_mul_div, hn, h0]
  · suffices repOp π μ (fun g => conj (χ g : ℂ) / μ.real univ) = 0 by
      rw [this]; exact ⟨isTraceClass_zero, trace_zero⟩
    by_contra hP
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 hP
    set w := repOp π μ (fun g => conj (χ g : ℂ) / μ.real univ) v with hw
    have hw0 : w ≠ 0 := hv
    have he : ∀ g, π g w = (χ g : ℂ) • w := fun g => by
      rw [hw, hπ.repOp_apply hf (hs _), ← (π g).integral_comp_comm (hπ.isRepOp hf (hs _) v).1, ← integral_smul,
        ← integral_mul_left_eq_self (fun x => (χ g : ℂ) • (conj (χ x : ℂ) / μ.real univ) • π x v) g]
      refine integral_congr_ae (.of_forall fun x => ?_)
      simp only [map_smul, map_mul, smul_smul, Circle.coe_mul, ContinuousLinearMap.mul_apply]
      rw [← mul_div_assoc, ← mul_assoc, mul_comm (χ g : ℂ), hn, one_mul]
    have htop := (hirr.2 _ (isIrredSubrep_span_singleton hw0 fun g => ⟨_, he g⟩).1).resolve_left (by simpa using hw0)
    have hall : ∀ g x, π g x = (χ g : ℂ) • x := fun g x => by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 (htop ▸ Submodule.mem_top : x ∈ ℂ ∙ w)
      rw [map_smul, he, smul_comm]
    have hu : ‖((‖w‖⁻¹ : ℝ) : ℂ) • w‖ = 1 := by simp [norm_smul, hw0]
    have hsp : (ℂ ∙ ((‖w‖⁻¹ : ℝ) : ℂ) • w) = ⊤ := by
      rw [Submodule.span_singleton_smul_eq (by simpa using hw0), htop]
    refine hne ⟨((LinearIsometryEquiv.toSpanUnitSingleton _ hu).trans (LinearIsometryEquiv.ofTop U _ hsp)).symm,
      fun g x => ?_⟩
    rw [hall, map_smul]
    rfl
  · haveI : CompactSpace (cent s) := isCompact_iff_compactSpace.1 hT
    convert hasOrbInt_of_finite (dh := μ) (dt := dt) (f := fun g => conj (χ g : ℂ) / μ.real univ)
      ((hf.comp (f := fun x => x⁻¹ * s * x) (by fun_prop)).integrable_of_hasCompactSupport (hs _)) using 2
    have : ∀ x, χ (x⁻¹ * s * x) = χ s := fun x => by rw [map_mul, map_mul, map_inv, mul_right_comm]; simp
    simp only [this, integral_const, Complex.real_smul]
    field_simp

def circleMat : Circle →* Matrix (Fin 1) (Fin 1) ℂ := (Matrix.scalar (Fin 1)).toMonoidHom.comp Circle.coeHom

example : ¬ IsRegSS (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧ IsRegSS (Matrix.diagonal ![(1 : ℂ), -1]) := by
  constructor
  · rw [IsRegSS, ← Matrix.diagonal_one, Matrix.charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]
    exact fun h => zero_ne_one (h (a₁ := 0) (a₂ := 1) rfl)
  · rw [IsRegSS, Matrix.charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]
    intro a b h
    fin_cases a <;> fin_cases b <;> simp at h ⊢ <;> norm_num at h

end Real

end GlobalTheory.Orb
