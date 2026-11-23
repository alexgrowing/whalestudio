import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt

noncomputable section

open MeasureTheory Filter Topology UpperTheory.ConvolutionTheory.L1
open scoped ComplexConjugate Pointwise

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.Amp

section Cpt

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K]

omit [Group K] [IsTopologicalGroup K] [SecondCountableTopology K] in
theorem intK (κ : Measure K) [IsFiniteMeasure κ] {f : K → ℂ} (hf : Continuous f) : Integrable f κ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

omit [Group K] [IsTopologicalGroup K] in
theorem swapK {A : Type} [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] (α : Measure A) [IsFiniteMeasure α]
    (κ : Measure K) [IsFiniteMeasure κ] {f : A → K → ℂ} (hf : Continuous (Function.uncurry f)) :
    ∫ x, ∫ y, f x y ∂κ ∂α = ∫ y, ∫ x, f x y ∂α ∂κ :=
  integral_integral_swap (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem int_inv (κ : Measure K) [IsProbabilityMeasure κ] [κ.IsMulLeftInvariant] {f : K → ℂ} (hf : Continuous f) :
    ∫ k, f k⁻¹ ∂κ = ∫ k, f k ∂κ := by
  have h := swapK κ κ (f := fun x y => f (x⁻¹ * y)) (by unfold Function.uncurry; fun_prop)
  have h1 : ∀ x, ∫ y, f (x⁻¹ * y) ∂κ = ∫ y, f y ∂κ := fun x => integral_mul_left_eq_self f x⁻¹
  have h2 : ∀ y, ∫ x, f (x⁻¹ * y) ∂κ = ∫ x, f x⁻¹ ∂κ := fun y => by
    rw [← integral_mul_left_eq_self _ y]
    simp
  simp only [h1, h2, integral_const, probReal_univ, one_smul] at h
  exact h.symm

theorem int_surj {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
    (α : Measure A) [IsProbabilityMeasure α] [α.IsMulRightInvariant] (κ : Measure K) [IsProbabilityMeasure κ] [κ.IsMulLeftInvariant]
    (s : A → K) (hs : Continuous s) (hm : ∀ x y, s (x * y) = s x * s y) (ho : Function.Surjective s) {f : K → ℂ} (hf : Continuous f) :
    ∫ k, f k ∂κ = ∫ x, f (s x) ∂α := by
  have h := swapK α κ (f := fun x y => f (s x * y)) (by unfold Function.uncurry; fun_prop)
  have h1 : ∀ x, ∫ y, f (s x * y) ∂κ = ∫ y, f y ∂κ := fun x => integral_mul_left_eq_self f (s x)
  have h2 : ∀ y, ∫ x, f (s x * y) ∂α = ∫ x, f (s x) ∂α := fun y => by
    obtain ⟨z, rfl⟩ := ho y
    simp only [← hm]
    exact integral_mul_right_eq_self (fun x => f (s x)) z
  simpa only [h1, h2, integral_const, probReal_univ, one_smul] using h

theorem idem_fin (κ : Measure K) [IsProbabilityMeasure κ] [κ.IsMulLeftInvariant] {e : K → ℂ} (he : Continuous e)
    (hi : ∀ k, ∫ h, e h * e (h⁻¹ * k) ∂κ = e k) :
    ∃ V : Submodule ℂ C(K, ℂ), FiniteDimensional ℂ V ∧ ∀ h : K, ∃ f ∈ V, ∀ k, f k = e (h * k) := by
  let V : Submodule ℂ C(K, ℂ) :=
    { carrier := {f | ∀ k, ∫ t, f t * e (t⁻¹ * k) ∂κ = f k}
      add_mem' := fun {f g} hf hg k => by
        simp only [ContinuousMap.add_apply, add_mul]
        rw [integral_add (intK κ (by fun_prop)) (intK κ (by fun_prop)), hf k, hg k]
      zero_mem' := fun k => by simp
      smul_mem' := fun c f hf k => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
        rw [hf k] }
  refine ⟨V, ?_, fun h => ⟨⟨fun k => e (h * k), by fun_prop⟩, fun k => ?_, fun _ => rfl⟩⟩
  · let c : C(K, C(K, ℂ)) := ContinuousMap.curry ⟨fun p : K × K => e (p.2⁻¹ * p.1), by fun_prop⟩
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun k : K => c ⁻¹' Metric.ball (c k) (1 / 2))
      (fun k => Metric.isOpen_ball.preimage c.continuous) (fun k _ => Set.mem_iUnion.2 ⟨k, by simp⟩)
    let ev : V →ₗ[ℂ] (s → ℂ) :=
      { toFun := fun f i => f.1 i.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero ev).2 fun f hf => ?_)
    have hb : ‖f.1‖ ≤ ‖f.1‖ * (1 / 2) := by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun k => ?_
      obtain ⟨i, hi', hk⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ k))
      have h0 : f.1 i = 0 := congrFun hf ⟨i, hi'⟩
      have hk' : ‖c k - c i‖ ≤ 1 / 2 := by
        have : dist (c k) (c i) < 1 / 2 := hk
        rw [dist_eq_norm] at this
        exact this.le
      have h1 : f.1 k = ∫ t, f.1 t * (c k - c i) t ∂κ := by
        have e1 : ∀ t, f.1 t * (c k - c i) t = f.1 t * e (t⁻¹ * k) - f.1 t * e (t⁻¹ * i) := fun t => by
          rw [← mul_sub]; rfl
        simp only [e1]
        rw [integral_sub (intK κ (by fun_prop)) (intK κ (by fun_prop)), f.2 k, f.2 i, h0, sub_zero]
      rw [h1]
      refine (norm_integral_le_of_norm_le_const (C := ‖f.1‖ * (1 / 2)) (Eventually.of_forall fun t => ?_)).trans (by simp)
      rw [norm_mul]
      exact mul_le_mul (f.1.norm_coe_le_norm t) (((c k - c i).norm_coe_le_norm t).trans hk') (norm_nonneg _) (norm_nonneg _)
    have : ‖f.1‖ = 0 := by linarith [norm_nonneg f.1]
    exact Subtype.ext (norm_eq_zero.1 this)
  · change ∫ t, e (h * t) * e (t⁻¹ * k) ∂κ = e (h * k)
    rw [← hi (h * k), ← integral_mul_left_eq_self (fun t => e t * e (t⁻¹ * (h * k))) h]
    simp [mul_assoc]

end Cpt

section Grp

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {K : Subgroup G} [CompactSpace K]

local instance : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)

def ec (κ : Measure K) (e : K → ℂ) (β : G → ℂ) (g : G) : ℂ := ∫ k, e k * β ((k : G)⁻¹ * g) ∂κ

variable (κ : Measure K) [IsProbabilityMeasure κ] (ν : Measure G) [ν.IsHaarMeasure]

theorem swapKG {f : K → G → ℂ} (hf : Continuous (Function.uncurry f)) {C : Set G} (hC : IsCompact C)
    (h0 : ∀ k g, g ∉ C → f k g = 0) : ∫ k, ∫ g, f k g ∂ν ∂κ = ∫ g, ∫ k, f k g ∂κ ∂ν :=
  integral_integral_swap (hf.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_univ.prod hC) fun p hp => h0 p.1 p.2 fun h => hp ⟨trivial, h⟩))

theorem contK {X : Type} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X] {f : X → K → ℂ}
    (hf : Continuous (Function.uncurry f)) : Continuous fun x => ∫ k, f x k ∂κ := by
  simpa only [Measure.restrict_univ] using continuous_parametric_integral_of_continuous (μ := κ) hf isCompact_univ

theorem contG {β : G → ℂ} (hβ : Continuous β) (hc : HasCompactSupport β) {f : G → G → ℂ}
    (hf : Continuous (Function.uncurry f)) : Continuous fun x => ∫ g, β g * f x g ∂ν := by
  have h : (fun x => ∫ g, β g * f x g ∂ν) = fun x => ∫ g in tsupport β, β g * f x g ∂ν := by
    funext x
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  rw [h]
  exact continuous_parametric_integral_of_continuous (f := fun x g => β g * f x g) ((hβ.comp continuous_snd).mul hf) hc

theorem ec_cont {e : K → ℂ} (he : Continuous e) {β : G → ℂ} (hβ : Continuous β) : Continuous (ec κ e β) :=
  contK κ (f := fun g (k : K) => e k * β ((k : G)⁻¹ * g)) (by unfold Function.uncurry; fun_prop)

theorem cptKC {β : G → ℂ} (hc : HasCompactSupport β) : IsCompact ((K : Set G) * tsupport β) :=
  (isCompact_iff_compactSpace.2 ‹CompactSpace K›).mul hc

theorem zeroKC {β : G → ℂ} (k : K) {g : G} (hg : g ∉ (K : Set G) * tsupport β) : β ((k : G)⁻¹ * g) = 0 := by
  by_contra h
  have := Set.mul_mem_mul (s := (K : Set G)) k.2 (subset_tsupport β h)
  exact hg (by simpa using this)

theorem ec_cs (e : K → ℂ) {β : G → ℂ} (hc : HasCompactSupport β) : HasCompactSupport (ec κ e β) :=
  HasCompactSupport.intro (cptKC (K := K) hc) fun g hg => by simp [ec, zeroKC _ hg]

theorem ec_adj {e : K → ℂ} (he : Continuous e) {β : G → ℂ} (hβ : Continuous β) (hc : HasCompactSupport β) {T : G → ℂ}
    (hT : Continuous T) : ∫ y, ec κ e β y * T y ∂ν = ∫ y, β y * ∫ k, e k * T (k * y) ∂κ ∂ν := by
  calc ∫ y, ec κ e β y * T y ∂ν = ∫ y, ∫ k : K, e k * β ((k : G)⁻¹ * y) * T y ∂κ ∂ν := by
        simp only [ec, integral_mul_const]
    _ = ∫ k : K, ∫ y, e k * β ((k : G)⁻¹ * y) * T y ∂ν ∂κ :=
        (swapKG κ ν (by unfold Function.uncurry; fun_prop) (cptKC (K := K) hc) fun k g hg => by simp [zeroKC k hg]).symm
    _ = ∫ k : K, ∫ y, β y * (e k * T (k * y)) ∂ν ∂κ := by
        congr 1; funext k
        rw [← integral_mul_left_eq_self _ (k : G)]
        congr 1; funext y
        rw [inv_mul_cancel_left]; ring
    _ = ∫ y, ∫ k : K, β y * (e k * T (k * y)) ∂κ ∂ν :=
        swapKG κ ν (by unfold Function.uncurry; fun_prop) hc fun k g hg => by simp [image_eq_zero_of_notMem_tsupport hg]
    _ = _ := by simp only [integral_const_mul]

theorem ec_idem [κ.IsMulLeftInvariant] {e : K → ℂ} (he : Continuous e) (hi : ∀ k, ∫ h, e h * e (h⁻¹ * k) ∂κ = e k)
    {β : G → ℂ} (hβ : Continuous β) : ec κ e (ec κ e β) = ec κ e β := by
  funext g
  calc ec κ e (ec κ e β) g = ∫ k : K, ∫ h : K, e k * e (k⁻¹ * h) * β ((h : G)⁻¹ * g) ∂κ ∂κ := by
        unfold ec
        congr 1; funext k
        rw [← integral_const_mul, ← integral_mul_left_eq_self _ k⁻¹]
        congr 1; funext h
        simp [mul_assoc]
    _ = ∫ h : K, ∫ k : K, e k * e (k⁻¹ * h) * β ((h : G)⁻¹ * g) ∂κ ∂κ := swapK κ κ (by unfold Function.uncurry; fun_prop)
    _ = _ := by simp only [integral_mul_const, hi, ec]

theorem cv_adj {b c ψ : G → ℂ} (hb : Continuous b) (hb' : HasCompactSupport b) (hc : Continuous c) (hc' : HasCompactSupport c)
    (hψ : Continuous ψ) : ∫ g, cv ν b c g * ψ g ∂ν = ∫ y, b y * ∫ z, c z * ψ (y * z) ∂ν ∂ν := by
  have hint : Integrable (Function.uncurry fun g y : G => b y * c (y⁻¹ * g) * ψ g) (ν.prod ν) := by
    refine Continuous.integrable_of_hasCompactSupport (by unfold Function.uncurry; fun_prop) ?_
    refine HasCompactSupport.intro (K := (tsupport b * tsupport c) ×ˢ tsupport b) ((IsCompact.mul hb' hc').prod hb') fun p hp => ?_
    by_contra h
    have h1 := left_ne_zero_of_mul h
    have h2 : b p.2 ≠ 0 := left_ne_zero_of_mul h1
    have := Set.mul_mem_mul (subset_tsupport _ h2) (subset_tsupport c (right_ne_zero_of_mul h1))
    exact hp ⟨by simpa using this, subset_tsupport _ h2⟩
  calc ∫ g, cv ν b c g * ψ g ∂ν = ∫ g, ∫ y, b y * c (y⁻¹ * g) * ψ g ∂ν ∂ν := by simp only [cv, integral_mul_const]
    _ = ∫ y, ∫ g, b y * c (y⁻¹ * g) * ψ g ∂ν ∂ν := integral_integral_swap hint
    _ = _ := by
        congr 1; funext y
        rw [← integral_const_mul, ← integral_mul_left_eq_self _ y]
        congr 1; funext z
        rw [inv_mul_cancel_left, mul_assoc]

theorem bi_sq [κ.IsMulLeftInvariant] {e : K → ℂ} (he : Continuous e) (hs : ∀ k, e k⁻¹ = conj (e k)) {b : G → ℂ} (hb : Continuous b)
    (hc : HasCompactSupport b) (hf : ec κ e b = b) (g : G) :
    ∫ k : K, e k * cv ν b (fun x => conj (b x⁻¹)) ((k : G)⁻¹ * g) ∂κ = cv ν b (fun x => conj (b x⁻¹)) g ∧
      ∫ k : K, cv ν b (fun x => conj (b x⁻¹)) (g * (k : G)⁻¹) * e k ∂κ = cv ν b (fun x => conj (b x⁻¹)) g := by
  have hz : ∀ y, y ∉ tsupport b → b y = 0 := fun y => image_eq_zero_of_notMem_tsupport
  constructor
  · have h := ec_adj κ ν he hb hc (T := fun y => conj (b (y⁻¹ * g)⁻¹)) (by fun_prop)
    rw [hf] at h
    refine Eq.trans ?_ h.symm
    simp only [cv, ← integral_const_mul]
    rw [swapKG κ ν (by unfold Function.uncurry; fun_prop) hc fun k y hy => by simp [hz y hy]]
    congr 1; funext y; congr 1; funext k
    rw [mul_left_comm]
    simp [mul_assoc]
  · simp only [cv, ← integral_mul_const]
    rw [swapKG κ ν (by unfold Function.uncurry; fun_prop) hc fun k y hy => by simp [hz y hy]]
    congr 1; funext y
    simp only [mul_assoc, integral_const_mul]
    congr 1
    rw [← congrFun hf (y⁻¹ * g)⁻¹, ec, ← integral_conj, ← int_inv κ (by fun_prop)]
    congr 1; funext k
    simp [hs, mul_assoc, mul_comm]

theorem avg_near {β : G → ℝ} (hβ : Continuous β) (hc : HasCompactSupport β) (h0 : ∀ x, 0 ≤ β x) {T : G → ℂ} (hT : Continuous T)
    {c : ℂ} {r : ℝ} (h : ∀ y, β y ≠ 0 → ‖T y - c‖ ≤ r) :
    ‖∫ y, (β y : ℂ) * T y ∂ν - (∫ y, β y ∂ν : ℝ) * c‖ ≤ (∫ y, β y ∂ν) * r := by
  have hc' : HasCompactSupport fun y => (β y : ℂ) := hc.comp_left Complex.ofReal_zero
  have i1 : Integrable (fun y => (β y : ℂ) * T y) ν := Continuous.integrable_of_hasCompactSupport (by fun_prop) hc'.mul_right
  have i2 : Integrable (fun y => (β y : ℂ) * c) ν := Continuous.integrable_of_hasCompactSupport (by fun_prop) hc'.mul_right
  rw [← integral_complex_ofReal, ← integral_mul_const, ← integral_sub i1 i2, ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((hβ.integrable_of_hasCompactSupport hc).mul_const r) (Eventually.of_forall fun y => ?_)
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 y)]
  by_cases hy : β y = 0
  · simp [hy]
  · exact mul_le_mul_of_nonneg_left (h y hy) (h0 y)

theorem sq_ne [κ.IsMulLeftInvariant] [ν.IsInvInvariant] {e : K → ℂ} (he : Continuous e) (hs : ∀ k, e k⁻¹ = conj (e k))
    {ψ : G → ℂ} (hψ : Continuous ψ) (hf : ∀ w, ∫ k : K, e k * ψ (w * k) ∂κ = ψ w) (h1 : ψ 1 ≠ 0) :
    ∃ O ∈ 𝓝 (1 : G), ∀ β : G → ℝ, Continuous β → HasCompactSupport β → (∀ x, 0 ≤ β x) → (∃ x, β x ≠ 0) → (∀ x, β x ≠ 0 → x ∈ O) →
      ∫ g, cv ν (ec κ e fun x => β x) (fun x => conj (ec κ e (fun x => β x) x⁻¹)) g * ψ g ∂ν ≠ 0 := by
  let Ψ : G → ℂ := fun u => ∫ k : K, e k * ψ (k * u) ∂κ
  have hΨ : Continuous Ψ := contK κ (f := fun u (k : K) => e k * ψ (k * u)) (by unfold Function.uncurry; fun_prop)
  have hΨ1 : Ψ 1 = ψ 1 := by simpa [Ψ] using hf 1
  have hr : 0 < ‖ψ 1‖ / 2 := half_pos (norm_pos_iff.2 h1)
  have hn : ∀ᶠ p : G × G in 𝓝 (1, 1), ‖Ψ (p.1 * p.2⁻¹) - ψ 1‖ < ‖ψ 1‖ / 2 := by
    have hcc : Continuous fun p : G × G => ‖Ψ (p.1 * p.2⁻¹) - ψ 1‖ := by fun_prop
    exact hcc.continuousAt.eventually_lt continuousAt_const (by simpa [hΨ1] using norm_pos_iff.2 h1)
  rw [nhds_prod_eq] at hn
  obtain ⟨O₁, h₁, O₂, h₂, hO⟩ := Filter.mem_prod_iff.1 hn
  refine ⟨O₁ ∩ O₂, inter_mem h₁ h₂, fun β hβ hc h0 hx hsup => ?_⟩
  have hc' : HasCompactSupport fun y => (β y : ℂ) := hc.comp_left Complex.ofReal_zero
  have hβ' : Continuous fun y => (β y : ℂ) := by fun_prop
  have hb := ec_cont κ he hβ'
  have hb' := ec_cs κ e hc'
  have hbs : HasCompactSupport fun x => conj (ec κ e (fun x => β x) x⁻¹) :=
    (hb'.comp_homeomorph (Homeomorph.inv G)).comp_left (g := conj) (map_zero _)
  have hC : ∀ y, ∫ z, conj (ec κ e (fun x => β x) z⁻¹) * ψ (y * z) ∂ν = ∫ z, (β z : ℂ) * ψ (y * z⁻¹) ∂ν := fun y => by
    have e1 : ∀ z, conj (ec κ e (fun x => β x) z) = ec κ (fun k => e k⁻¹) (fun x => β x) z := fun z => by
      simp only [ec, ← integral_conj, map_mul, Complex.conj_ofReal, hs]
    rw [← integral_inv_eq_self]
    simp only [inv_inv, e1]
    rw [ec_adj κ ν (by fun_prop) hβ' hc' (by fun_prop)]
    congr 1; funext z
    rw [← hf (y * z⁻¹), ← int_inv κ (f := fun k : K => e k * ψ (y * z⁻¹ * k)) (by fun_prop)]
    simp [mul_assoc]
  have hT : Continuous fun y => ∫ z, (β z : ℂ) * ψ (y * z⁻¹) ∂ν :=
    contG ν hβ' hc' (f := fun y z => ψ (y * z⁻¹)) (by unfold Function.uncurry; fun_prop)
  have hH : Continuous fun y => ∫ z, (β z : ℂ) * Ψ (y * z⁻¹) ∂ν :=
    contG ν hβ' hc' (f := fun y z => Ψ (y * z⁻¹)) (by unfold Function.uncurry; fun_prop)
  have hD : ∀ y, ∫ k : K, e k * ∫ z, (β z : ℂ) * ψ (k * y * z⁻¹) ∂ν ∂κ = ∫ z, (β z : ℂ) * Ψ (y * z⁻¹) ∂ν := fun y => by
    simp only [Ψ, ← integral_const_mul]
    rw [swapKG κ ν (by unfold Function.uncurry; fun_prop) hc fun k z hz => by simp [image_eq_zero_of_notMem_tsupport hz]]
    simp only [mul_left_comm (e _), mul_assoc]
  rw [cv_adj ν hb hb' (by fun_prop) hbs hψ]
  simp only [hC]
  rw [ec_adj κ ν he hβ' hc' hT]
  simp only [hD]
  obtain ⟨x, hx⟩ := hx
  have hm : 0 < ∫ y, β y ∂ν := hβ.integral_pos_of_hasCompactSupport_nonneg_nonzero hc h0 hx
  have key := avg_near ν hβ hc h0 hH (c := (∫ y, β y ∂ν : ℝ) * ψ 1) (r := (∫ y, β y ∂ν) * (‖ψ 1‖ / 2)) fun y hy =>
    avg_near ν hβ hc h0 (T := fun z => Ψ (y * z⁻¹)) (by fun_prop) fun z hz =>
      le_of_lt (hO (Set.mk_mem_prod (hsup y hy).1 (hsup z hz).2))
  intro hz
  rw [hz, zero_sub, norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hm.le] at key
  have := mul_pos hm (mul_pos hm hr)
  linarith

theorem ec_fin [κ.IsMulLeftInvariant] {e : K → ℂ} (he : Continuous e) (hi : ∀ k, ∫ h, e h * e (h⁻¹ * k) ∂κ = e k)
    {β : G → ℂ} (hβ : Continuous β) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun g : G => ec κ e β ((k : G) * g))) := by
  obtain ⟨V, hV, hh⟩ := idem_fin κ he hi
  let Φ : C(K, ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun f => ec κ f β
      map_add' := fun f f' => by
        funext g
        simp only [ec, ContinuousMap.add_apply, add_mul, Pi.add_apply]
        exact integral_add (intK κ (by fun_prop)) (intK κ (by fun_prop))
      map_smul' := fun c f => by
        funext g
        simp only [ec, ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul, Pi.smul_apply, RingHom.id_apply] }
  refine Submodule.finiteDimensional_of_le (S₂ := V.map Φ) (Submodule.span_le.2 ?_)
  rintro _ ⟨h, rfl⟩
  obtain ⟨f, hf, hfe⟩ := hh h
  refine ⟨f, hf, funext fun g => ?_⟩
  change ec κ f β g = ec κ e β (h * g)
  unfold ec
  rw [← integral_mul_left_eq_self (fun k : K => e k * β ((k : G)⁻¹ * (h * g))) h]
  simp [hfe, mul_assoc]

end Grp

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.Amp
