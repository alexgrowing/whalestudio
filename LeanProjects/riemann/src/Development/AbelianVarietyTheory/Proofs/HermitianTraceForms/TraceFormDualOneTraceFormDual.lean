import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement

namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open scoped nonZeroDivisors

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem isIntegral_cc {a : E} (h : IsIntegral ℤ a) : IsIntegral ℤ (cc a) :=
  (IsCMField.ringOfIntegersComplexConj E ⟨a, h⟩).isIntegral_coe

theorem trace_cc (a : E) : Algebra.trace ℚ E (cc a) = Algebra.trace ℚ E a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a

def conjFrac : FractionalIdeal (𝓞 E)⁰ E ≃+* FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.ringEquivOfRingEquiv E E (IsCMField.ringOfIntegersComplexConj E).toRingEquiv

private theorem fractionRing_conj (x : E) :
    IsFractionRing.ringEquivOfRingEquiv (K := E) (L := E)
      (IsCMField.ringOfIntegersComplexConj E).toRingEquiv x = cc x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  rw [map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, cc, map_div₀]
  rfl

theorem mem_conjFrac {a : FractionalIdeal (𝓞 E)⁰ E} {x : E} : x ∈ conjFrac a ↔ cc x ∈ a := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := (congrArg cc (fractionRing_conj y)).trans (cc_cc y)
    exact h.symm ▸ hy
  · intro h
    exact ⟨cc x, h, (fractionRing_conj (cc x)).trans (cc_cc x)⟩

theorem cc_mem_conjFrac {a : FractionalIdeal (𝓞 E)⁰ E} {x : E} : cc x ∈ conjFrac a ↔ x ∈ a := by
  rw [mem_conjFrac, cc_cc]

@[simp] theorem conjFrac_conjFrac (a : FractionalIdeal (𝓞 E)⁰ E) : conjFrac (conjFrac a) = a := by
  ext x; rw [mem_conjFrac, cc_mem_conjFrac]

theorem conjFrac_ne_zero {a : FractionalIdeal (𝓞 E)⁰ E} (ha : a ≠ 0) : conjFrac a ≠ 0 :=
  (map_ne_zero_iff _ conjFrac.injective).2 ha

theorem conjFrac_inv (a : FractionalIdeal (𝓞 E)⁰ E) : conjFrac a⁻¹ = (conjFrac a)⁻¹ :=
  map_inv₀ _ a

theorem conjFrac_spanSingleton (x : E) :
    conjFrac (FractionalIdeal.spanSingleton (𝓞 E)⁰ x) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (cc x) := by
  ext y
  rw [mem_conjFrac, FractionalIdeal.mem_spanSingleton, FractionalIdeal.mem_spanSingleton]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨IsCMField.ringOfIntegersComplexConj E z, ?_⟩
    rw [← cc_cc y, ← hz, Algebra.smul_def, Algebra.smul_def, cc_mul]; rfl
  · rintro ⟨z, hz⟩
    refine ⟨IsCMField.ringOfIntegersComplexConj E z, ?_⟩
    rw [← hz, Algebra.smul_def, Algebra.smul_def, cc_mul, cc_cc]; rfl

omit [IsCMField E] in
theorem mem_one_fractionalIdeal_iff {x : E} :
    x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ IsIntegral ℤ x := by
  rw [FractionalIdeal.mem_one_iff]
  exact ⟨fun ⟨z, hz⟩ => hz ▸ z.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩

omit [IsCMField E] in

theorem mem_inv_different_iff {x : E} :
    x ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ↔
      ∀ a : E, IsIntegral ℤ a → ∃ k : ℤ, Algebra.trace ℚ E (x * a) = k := by
  rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv,
    FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))]
  refine forall_congr' fun a => ?_
  rw [mem_one_fractionalIdeal_iff, Algebra.traceForm_apply]
  exact imp_congr_right fun _ => ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

omit [IsCMField E] in
theorem coe_different_ne_zero :
    ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
  rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)]
  exact inv_ne_zero (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)

theorem conjFrac_different :
    conjFrac ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) =
      (differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) := by
  apply inv_injective
  rw [← conjFrac_inv]
  ext x
  rw [mem_conjFrac, mem_inv_different_iff, mem_inv_different_iff]
  constructor
  · intro h a ha
    rw [← trace_cc, cc_mul]
    exact h _ (isIntegral_cc ha)
  · intro h a ha
    rw [← trace_cc, cc_mul, cc_cc]
    exact h _ (isIntegral_cc ha)

omit [IsCMField E] in
theorem fractionalIdeal_mul_smul (a b : FractionalIdeal (𝓞 E)⁰ E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) :
    ((a * b : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) • Λ =
      (a : Submodule (𝓞 E) E) • (b : Submodule (𝓞 E) E) • Λ := by
  rw [FractionalIdeal.coe_mul]
  exact Submodule.smul_assoc _ _ _

omit [IsCMField E] in
theorem fractionalIdeal_one_smul (Λ : Submodule (𝓞 E) (Fin r → E)) :
    ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) • Λ = Λ := by
  rw [FractionalIdeal.coe_one]
  exact Submodule.one_smul _

omit [IsCMField E] in
theorem fractionalIdeal_smul_inv_smul {a : FractionalIdeal (𝓞 E)⁰ E} (ha : a ≠ 0)
    (Λ : Submodule (𝓞 E) (Fin r → E)) :
    (a : Submodule (𝓞 E) E) • ((a⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) • Λ = Λ := by
  rw [← fractionalIdeal_mul_smul, mul_inv_cancel₀ ha, fractionalIdeal_one_smul]

omit [IsCMField E] in
theorem fractionalIdeal_inv_smul_smul {a : FractionalIdeal (𝓞 E)⁰ E} (ha : a ≠ 0)
    (Λ : Submodule (𝓞 E) (Fin r → E)) :
    ((a⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) • (a : Submodule (𝓞 E) E) • Λ = Λ := by
  rw [← fractionalIdeal_mul_smul, inv_mul_cancel₀ ha, fractionalIdeal_one_smul]

omit [IsCMField E] in

theorem isLattice_fractionalIdeal_smul {a : FractionalIdeal (𝓞 E)⁰ E} (ha : a ≠ 0)
    {Λ : Submodule (𝓞 E) (Fin r → E)} (hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice ((a : Submodule (𝓞 E) E) • Λ) := by
  constructor
  · obtain ⟨s, hs⟩ := FractionalIdeal.fg_of_isUnit a ha.isUnit
    obtain ⟨t, ht⟩ := hΛ.1
    classical
    refine ⟨Finset.image₂ (· • ·) s t, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro x hx
      obtain ⟨α, hα, y, hy, rfl⟩ := Finset.mem_image₂.1 hx
      exact Submodule.smul_mem_smul (hs ▸ Submodule.subset_span hα)
        (ht ▸ Submodule.subset_span hy)
    · rw [Submodule.smul_le, ← hs, ← ht]
      intro α hα y hy
      induction hα using Submodule.span_induction with
      | mem α hα =>
        induction hy using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image₂_of_mem hα hy))
        | zero => simp
        | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
        | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ c hy
      | zero => simp
      | add α β _ _ hα hβ => rw [add_smul]; exact add_mem hα hβ
      | smul c α _ hα => rw [smul_assoc]; exact Submodule.smul_mem _ c hα
  · obtain ⟨α, hα0, hα⟩ : ∃ α : E, α ≠ 0 ∧ α ∈ a := by
      by_contra h
      push Not at h
      exact ha (FractionalIdeal.eq_zero_iff.2 fun x hx => by_contra fun h0 => h x h0 hx)
    rw [eq_top_iff, ← hΛ.2, Submodule.span_le]
    intro y hy
    have : y = α⁻¹ • α • y := by rw [smul_smul, inv_mul_cancel₀ hα0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.smul_mem_smul hα hy))

omit [NumberField E] [IsCMField E] in
theorem smul_mem_of_isIntegral (Λ : Submodule (𝓞 E) (Fin r → E)) {a : E} (ha : IsIntegral ℤ a)
    {y : Fin r → E} (hy : y ∈ Λ) : a • y ∈ Λ :=
  Λ.smul_mem (⟨a, ha⟩ : 𝓞 E) hy

theorem herm_add_right (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  simp [herm, mul_add, Finset.sum_add_distrib]

def hermDual (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    Submodule (𝓞 E) (Fin r → E) where
  carrier := {x | ∀ y ∈ Λ, IsIntegral ℤ (herm G x y)}
  add_mem' hx hx' y hy := by rw [herm_add_left]; exact (hx y hy).add (hx' y hy)
  zero_mem' y _ := by simpa [herm] using isIntegral_zero
  smul_mem' c x hx y hy := by
    change IsIntegral ℤ (herm G ((c : E) • x) y)
    rw [herm_smul_left]
    exact c.isIntegral_coe.mul (hx y hy)

variable {G : Matrix (Fin r) (Fin r) E} {Λ Λ₁ Λ₂ : Submodule (𝓞 E) (Fin r → E)}

theorem mem_hermDual {x : Fin r → E} :
    x ∈ hermDual G Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm G x y) := Iff.rfl

theorem mem_smul_hermDual_iff {b : FractionalIdeal (𝓞 E)⁰ E} (hb : b ≠ 0) {x : Fin r → E} :
    x ∈ (b : Submodule (𝓞 E) E) • hermDual G Λ ↔ ∀ y ∈ Λ, herm G x y ∈ b := by
  constructor
  · intro hx y hy
    refine Submodule.smul_induction_on (p := fun x => herm G x y ∈ b) hx ?_ ?_
    · intro β hβ w hw
      rw [herm_smul_left, ← mul_one b]
      exact FractionalIdeal.mul_mem_mul hβ (mem_one_fractionalIdeal_iff.2 (hw y hy))
    · intro u v hu hv
      rw [herm_add_left]
      exact (b : Submodule (𝓞 E) E).add_mem hu hv
  · intro h
    have h1 : (1 : E) ∈ b * b⁻¹ := by
      rw [mul_inv_cancel₀ hb]; exact FractionalIdeal.one_mem_one _
    rw [← one_smul E x]
    refine FractionalIdeal.mul_induction_on (C := fun t : E =>
      t • x ∈ (b : Submodule (𝓞 E) E) • hermDual G Λ) h1 ?_ ?_
    · intro β hβ γ hγ
      rw [mul_smul]
      refine Submodule.smul_mem_smul hβ fun y hy => ?_
      rw [herm_smul_left, ← mem_one_fractionalIdeal_iff, ← inv_mul_cancel₀ hb]
      exact FractionalIdeal.mul_mem_mul hγ (h y hy)
    · intro u v hu hv
      rw [add_smul]
      exact add_mem hu hv

theorem hermDual_smul {a : FractionalIdeal (𝓞 E)⁰ E} (ha : a ≠ 0) :
    hermDual G ((a : Submodule (𝓞 E) E) • Λ) =
      (((conjFrac a)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) • hermDual G Λ := by
  ext x
  rw [mem_smul_hermDual_iff (inv_ne_zero (conjFrac_ne_zero ha)), mem_hermDual]
  constructor
  · intro h y hy
    rw [FractionalIdeal.mem_inv_iff (conjFrac_ne_zero ha)]
    intro α hα
    rw [mem_one_fractionalIdeal_iff, mul_comm, ← cc_cc α, ← herm_smul_right]
    exact h _ (Submodule.smul_mem_smul (mem_conjFrac.1 hα) hy)
  · intro h y hy
    refine Submodule.smul_induction_on (p := fun y => IsIntegral ℤ (herm G x y)) hy ?_ ?_
    · intro α hα w hw
      rw [herm_smul_right, mul_comm, ← mem_one_fractionalIdeal_iff]
      exact (FractionalIdeal.mem_inv_iff (conjFrac_ne_zero ha)).1 (h w hw) _
        (cc_mem_conjFrac.2 hα)
    · intro u v hu hv
      rw [herm_add_right]
      exact hu.add hv

def traceFormBilin (ξ : E) (G : Matrix (Fin r) (Fin r) E) : LinearMap.BilinForm ℚ (Fin r → E) :=
  LinearMap.mk₂ ℚ (EFf ξ G)
    (fun x x' y => by simp only [EFf, herm_add_left, mul_add, map_add])
    (fun c x y => by
      rw [EFf, EFf, ← algebraMap_smul E c x, herm_smul_left, mul_left_comm, ← Algebra.smul_def,
        map_smul])
    (fun x y y' => by simp only [EFf, herm_add_right, mul_add, map_add])
    (fun c x y => by
      have hc : cc (algebraMap ℚ E c) = algebraMap ℚ E c := by simp [cc]
      rw [EFf, EFf, ← algebraMap_smul E c y, herm_smul_right, hc, mul_left_comm,
        ← Algebra.smul_def, map_smul])

@[simp] theorem traceFormBilin_apply (ξ : E) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    traceFormBilin ξ G x y = EFf ξ G x y := rfl

theorem EFf_smul_left (ξ : E) (G : Matrix (Fin r) (Fin r) E) (a : E) (x y : Fin r → E) :
    EFf ξ G (a • x) y = EFf ξ G x (cc a • y) := by
  rw [EFf, EFf, herm_smul_left, herm_smul_right, cc_cc]

theorem traceFormBilin_nondegenerate {ξ : E} (hξ : ξ ≠ 0) (hG : G.det ≠ 0) :
    (traceFormBilin ξ G).Nondegenerate := by
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun x hx => ?_
  refine eq_zero_of_herm G hG x fun y => ?_
  have h : -ξ * herm G x y = 0 := eq_zero_of_trace _ fun β => by
    have := hx ((β : E) • y)
    rwa [traceFormBilin_apply, EFf, herm_smul_right, mul_left_comm] at this
  exact (mul_eq_zero.1 h).resolve_left (neg_ne_zero.2 hξ)

def traceFormDual (ξ : E) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    Submodule (𝓞 E) (Fin r → E) where
  carrier := {x | ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ G x y = k}
  add_mem' {x x'} hx hx' y hy := by
    obtain ⟨k, hk⟩ := hx y hy
    obtain ⟨k', hk'⟩ := hx' y hy
    refine ⟨k + k', ?_⟩
    rw [← traceFormBilin_apply, map_add, LinearMap.add_apply, traceFormBilin_apply,
      traceFormBilin_apply, hk, hk', Int.cast_add]
  zero_mem' y _ := ⟨0, by simp [EFf, herm]⟩
  smul_mem' c x hx y hy := by
    change ∃ k : ℤ, EFf ξ G ((c : E) • x) y = k
    rw [EFf_smul_left]
    exact hx _ (smul_mem_of_isIntegral Λ (isIntegral_cc c.isIntegral_coe) hy)

theorem mem_traceFormDual {ξ : E} {x : Fin r → E} :
    x ∈ traceFormDual ξ G Λ ↔ ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ G x y = k := Iff.rfl

theorem traceFormDual_eq {ξ : E} (hξ : ξ ≠ 0) :
    traceFormDual ξ G Λ =
      (((FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ *
        (differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)))⁻¹ : FractionalIdeal (𝓞 E)⁰ E) :
          Submodule (𝓞 E) E) • hermDual G Λ := by
  have hs : FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.2 hξ
  have key : ∀ t : E, t ∈ (FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ *
        (differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)))⁻¹ ↔
      ∀ a : E, IsIntegral ℤ a → ∃ k : ℤ, Algebra.trace ℚ E (-ξ * (a * t)) = k := by
    intro t
    rw [mul_inv, FractionalIdeal.spanSingleton_inv, FractionalIdeal.mem_singleton_mul]
    have e : ∀ a : E, -ξ * (a * t) = ξ * t * -a := fun a => by ring
    constructor
    · rintro ⟨y, hy, rfl⟩ a ha
      rw [e, mul_inv_cancel_left₀ hξ]
      exact mem_inv_different_iff.1 hy _ ha.neg
    · intro h
      refine ⟨ξ * t, mem_inv_different_iff.2 fun a ha => ?_, (inv_mul_cancel_left₀ hξ t).symm⟩
      have := h _ ha.neg
      rwa [e, neg_neg] at this
  ext x
  rw [mem_smul_hermDual_iff (inv_ne_zero (mul_ne_zero hs coe_different_ne_zero)),
    mem_traceFormDual]
  constructor
  · intro h y hy
    rw [key]
    intro a ha
    have := h _ (smul_mem_of_isIntegral Λ (isIntegral_cc ha) hy)
    rwa [EFf, herm_smul_right, cc_cc] at this
  · intro h y hy
    have := (key _).1 (h y hy) 1 isIntegral_one
    rwa [one_mul] at this

theorem hermDual_eq_smul_traceFormDual {ξ : E} (hξ : ξ ≠ 0) :
    hermDual G Λ =
      ((FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ *
        (differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) :
          Submodule (𝓞 E) E) • traceFormDual ξ G Λ := by
  rw [traceFormDual_eq hξ, fractionalIdeal_smul_inv_smul
    (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hξ) coe_different_ne_zero)]

omit [IsCMField E] in

theorem exists_rat_basis_of_isLattice (hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ (Fin r → E)),
      Submodule.span ℤ (Set.range b) = Λ.restrictScalars ℤ := by
  have : (Λ.restrictScalars ℤ).IsLattice ℚ := by
    constructor
    · have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ.1
      have : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
      exact Module.Finite.iff_fg.1 this
    · rw [eq_top_iff]
      intro x _
      obtain ⟨d, hd, hdx⟩ := exists_smul_mem (F := E) Λ (x := x) (hΛ.2 ▸ Submodule.mem_top)
      obtain ⟨e, he⟩ : ∃ e : 𝓞 E, e * d = (Algebra.norm ℤ d : 𝓞 E) := by
        have := Ideal.absNorm_mem (Ideal.span {d})
        rw [Ideal.absNorm_span_singleton, Ideal.mem_span_singleton'] at this
        obtain ⟨e, he⟩ := this
        rcases Int.natAbs_eq (Algebra.norm ℤ d) with h | h
        · exact ⟨e, by rw [he, h]; simp⟩
        · exact ⟨-e, by rw [neg_mul, he, h]; simp⟩
      have hn : (Algebra.norm ℤ d : ℚ) ≠ 0 := by
        exact_mod_cast Algebra.norm_ne_zero_iff.2 hd
      have h1 : (Algebra.norm ℤ d : ℚ) • x ∈ Λ := by
        have := Λ.smul_mem e hdx
        rwa [smul_smul, he, Int.cast_smul_eq_zsmul, ← Int.cast_smul_eq_zsmul ℚ] at this
      rw [← inv_smul_smul₀ hn x]
      exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  let b := Module.finBasis ℤ (Λ.restrictScalars ℤ)
  refine ⟨_, b.extendOfIsLattice ℚ, ?_⟩
  have h1 : Set.range (b.extendOfIsLattice ℚ) = (Λ.restrictScalars ℤ).subtype '' Set.range b := by
    rw [← Set.range_comp]
    congr 1
    exact funext fun i => b.extendOfIsLattice_apply ℚ i
  rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem exists_traceFormDual_eq {ξ : E} (hξ : ξ ≠ 0) (hG : G.det ≠ 0)
    (hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ) (φ : Λ →+ ℤ) :
    ∃ x ∈ traceFormDual ξ G Λ, ∀ y : Λ, (φ y : ℚ) = EFf ξ G x y := by
  obtain ⟨n, b, hb⟩ := exists_rat_basis_of_isLattice hΛ
  have hbm : ∀ i, b i ∈ Λ := fun i => by
    have : b i ∈ Λ.restrictScalars ℤ := hb ▸ Submodule.subset_span ⟨i, rfl⟩
    exact this
  let f : Module.Dual ℚ (Fin r → E) := b.constr ℚ fun i => (φ ⟨b i, hbm i⟩ : ℚ)
  have hf : ∀ y : Λ, (φ y : ℚ) = f y := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ Submodule.span ℤ (Set.range b) := hb ▸ hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
    have : (⟨∑ i, c i • b i, hy⟩ : Λ) = ∑ i, c i • (⟨b i, hbm i⟩ : Λ) := by
      ext1; simp
    rw [this, map_sum, Submodule.coe_sum, map_sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, Submodule.coe_smul_of_tower, map_zsmul, Module.Basis.constr_basis,
      smul_eq_mul, Int.cast_mul, zsmul_eq_mul]
  let x := ((traceFormBilin ξ G).toDual (traceFormBilin_nondegenerate hξ hG)).symm f
  have hx : ∀ y, EFf ξ G x y = f y := fun y =>
    LinearMap.BilinForm.apply_toDual_symm_apply (B := traceFormBilin ξ G) f y
  exact ⟨x, fun y hy => ⟨φ ⟨y, hy⟩, by rw [hx, hf]⟩, fun y => by rw [hx, hf]⟩

theorem eq_of_EFf_eq {ξ : E} (hξ : ξ ≠ 0) (hG : G.det ≠ 0) (hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ)
    {x x' : Fin r → E} (h : ∀ y ∈ Λ, EFf ξ G x y = EFf ξ G x' y) : x = x' := by
  obtain ⟨n, b, hb⟩ := exists_rat_basis_of_isLattice hΛ
  apply LinearMap.ker_eq_bot.1 (traceFormBilin_nondegenerate hξ hG).ker_eq_bot
  refine b.ext fun i => h _ ?_
  have : b i ∈ Λ.restrictScalars ℤ := hb ▸ Submodule.subset_span ⟨i, rfl⟩
  exact this

theorem perfect_iff_traceFormDual_eq {ξ : E} (hξ : ξ ≠ 0) (hG : G.det ≠ 0)
    (hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ) :
    ((∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ G x y = k) ∧
      ∀ φ : Λ →+ ℤ, ∃ x ∈ Λ, ∀ y : Λ, (φ y : ℚ) = EFf ξ G x y) ↔
    traceFormDual ξ G Λ = Λ := by
  constructor
  · rintro ⟨hint, hperf⟩
    refine le_antisymm (fun x hx => ?_) hint
    choose k hk using hx
    let φ : Λ →+ ℤ := AddMonoidHom.mk' (fun y => k y y.2) fun y y' => by
      apply Int.cast_injective (α := ℚ)
      rw [Int.cast_add, ← hk, ← hk, ← hk]
      exact map_add (traceFormBilin ξ G x) _ _
    obtain ⟨x', hx', h⟩ := hperf φ
    rw [eq_of_EFf_eq hξ hG hΛ (x := x) (x' := x') fun y hy => (hk y hy).trans (h ⟨y, hy⟩)]
    exact hx'
  · intro h
    refine ⟨fun x hx => ?_, fun φ => ?_⟩
    · rw [← h] at hx; exact hx
    · obtain ⟨x, hx, hφ⟩ := exists_traceFormDual_eq hξ hG hΛ φ
      exact ⟨x, h ▸ hx, hφ⟩

theorem perfect_iff_hermDual_eq {ξ : E} (hξ : ξ ≠ 0) (hG : G.det ≠ 0)
    (hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ) :
    ((∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ G x y = k) ∧
      ∀ φ : Λ →+ ℤ, ∃ x ∈ Λ, ∀ y : Λ, (φ y : ℚ) = EFf ξ G x y) ↔
    hermDual G Λ =
      ((FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ *
        (differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) :
          Submodule (𝓞 E) E) • Λ := by
  rw [perfect_iff_traceFormDual_eq hξ hG hΛ]
  constructor
  · intro h
    rw [hermDual_eq_smul_traceFormDual hξ, h]
  · intro h
    rw [traceFormDual_eq hξ, h, fractionalIdeal_inv_smul_smul
      (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hξ) coe_different_ne_zero)]

theorem hermDual_eq_self_iff :
    hermDual G Λ = Λ ↔ (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm G x y)) ∧
      ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm G x y)) → x ∈ Λ :=
  ⟨fun h => ⟨fun _ hx => (h.ge hx :), fun _ hx => h.le hx⟩, fun h => le_antisymm h.2 h.1⟩

end

end GlobalTheory
