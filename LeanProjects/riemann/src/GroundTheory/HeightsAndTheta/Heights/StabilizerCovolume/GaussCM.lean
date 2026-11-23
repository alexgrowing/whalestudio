import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements.Gauss

open NumberField Polynomial
open scoped Matrix ComplexConjugate

abbrev Em : Type := CyclotomicField 4 ℚ

instance : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩

instance cycl4 : IsCyclotomicExtension {4} ℚ Em := CyclotomicField.isCyclotomicExtension 4 ℚ

instance gaussian_isCyclotomic_four : IsCyclotomicExtension {2 ^ 2} ℚ Em := CyclotomicField.isCyclotomicExtension 4 ℚ

instance : IsCMField Em :=
  IsCyclotomicExtension.Rat.isCMField Em (S := {4}) ⟨4, Set.mem_singleton _, by norm_num⟩

def ζ : Em := IsCyclotomicExtension.zeta 4 ℚ Em

theorem hζ : IsPrimitiveRoot ζ 4 := IsCyclotomicExtension.zeta_spec 4 ℚ Em

theorem ζ_sq : ζ ^ 2 = -1 := by
  have h4 : ζ ^ 4 = 1 := hζ.pow_eq_one
  have h2 : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (l := 2) (by norm_num) (by norm_num)
  have h : (ζ ^ 2 - 1) * (ζ ^ 2 + 1) = ζ ^ 4 - 1 := by ring
  rw [h4, sub_self] at h
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (sub_eq_zero.1 h) h2
  · exact eq_neg_of_add_eq_zero_left h

theorem ζ_isIntegral : IsIntegral ℤ ζ := hζ.isIntegral (by norm_num)

theorem exists_of_mem_adjoin {R : Type} [CommRing R] [Algebra R Em] {x : Em}
    (hx : x ∈ Algebra.adjoin R ({ζ} : Set Em)) :
    ∃ a b : R, x = algebraMap R Em a + algebraMap R Em b * ζ := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨0, 1, by simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, d, rfl⟩ := hz
    exact ⟨a + c, b + d, by simp only [map_add]; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, d, rfl⟩ := hz
    refine ⟨a * c - b * d, a * d + b * c, ?_⟩
    simp only [map_sub, map_add, map_mul]
    linear_combination (algebraMap R Em b * algebraMap R Em d) * ζ_sq

theorem exists_rat (x : Em) : ∃ a b : ℚ, x = (a : Em) + (b : Em) * ζ := by
  have hx : x ∈ Algebra.adjoin ℚ ({ζ} : Set Em) := by
    rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]
    trivial
  obtain ⟨a, b, h⟩ := exists_of_mem_adjoin hx
  exact ⟨a, b, by rw [h, eq_ratCast, eq_ratCast]⟩

theorem exists_int {x : Em} (hx : IsIntegral ℤ x) : ∃ a b : ℤ, x = (a : Em) + (b : Em) * ζ := by
  have hcl := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow
    (p := 2) (k := 2) (ζ := ζ) (hcycl := gaussian_isCyclotomic_four) hζ
  obtain ⟨y, rfl⟩ := hcl.isIntegral_iff.1 hx
  obtain ⟨a, b, h⟩ := exists_of_mem_adjoin (R := ℤ) y.2
  refine ⟨a, b, Eq.trans ?_ (h.trans (by rw [eq_intCast, eq_intCast]))⟩
  rfl

theorem isIntegral_rep (a b : ℤ) : IsIntegral ℤ ((a : Em) + (b : Em) * ζ) := by
  have ha : IsIntegral ℤ (a : Em) := by simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ Em a))
  have hb : IsIntegral ℤ (b : Em) := by simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ Em b))
  exact ha.add (hb.mul ζ_isIntegral)

abbrev cc : Em ≃ₐ[maximalRealSubfield Em] Em := IsCMField.complexConj Em

def φ₀ : Em →+* ℂ := Classical.choice inferInstance

theorem emb_ζ (σ : Em →+* ℂ) : σ ζ = Complex.I ∨ σ ζ = -Complex.I := by
  have hs : σ ζ ^ 2 = -1 := by rw [← map_pow, ζ_sq, map_neg, map_one]
  have h : (σ ζ - Complex.I) * (σ ζ + Complex.I) = σ ζ ^ 2 - Complex.I ^ 2 := by ring
  rw [hs, Complex.I_sq, sub_self] at h
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

theorem ringHom_ext {σ σ' : Em →+* ℂ} (h : σ ζ = σ' ζ) : σ = σ' := by
  have : σ.toRatAlgHom = σ'.toRatAlgHom :=
    AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)
      (fun x hx => by rw [Set.mem_singleton_iff] at hx; subst hx; exact h)
  ext x
  exact congrArg (fun f : Em →ₐ[ℚ] ℂ => f x) this

theorem conj_emb_ζ (σ : Em →+* ℂ) : conj (σ ζ) = -σ ζ := by
  rcases emb_ζ σ with h | h <;> rw [h] <;> simp [Complex.conj_I]

theorem cc_ζ : cc ζ = -ζ := by
  apply φ₀.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg, conj_emb_ζ]

theorem cc_ratCast (q : ℚ) : cc (q : Em) = q := map_ratCast cc q

theorem cc_intCast (n : ℤ) : cc (n : Em) = n := map_intCast cc n

theorem cmType (σ : Em →+* ℂ) :
    (∃ τ : Unit, (fun _ => φ₀) τ = σ) ↔ ¬ ∃ τ : Unit, (fun _ => φ₀) τ = (starRingEnd ℂ).comp σ := by
  simp only [exists_const]
  constructor
  · rintro rfl h
    have h1 := congrArg (fun f : Em →+* ℂ => f ζ) h
    simp only [RingHom.coe_comp, Function.comp_apply, conj_emb_ζ] at h1
    have h0 : φ₀ ζ ≠ 0 := by rcases emb_ζ φ₀ with h | h <;> rw [h] <;> simp [Complex.I_ne_zero]
    exact h0 (by linear_combination h1 / 2)
  · intro h
    rcases emb_ζ σ with hs | hs <;> rcases emb_ζ φ₀ with hp | hp
    · exact ringHom_ext (hp.trans hs.symm)
    · exact absurd (ringHom_ext (by simp [hs, hp, Complex.conj_I])) h
    · exact absurd (ringHom_ext (by simp [hs, hp, Complex.conj_I])) h
    · exact ringHom_ext (hp.trans hs.symm)

theorem finrank_Em : Module.finrank ℚ Em = 2 := by
  rw [IsCyclotomicExtension.finrank Em (cyclotomic.irreducible_rat (n := 4) (by norm_num))]
  decide

theorem trace_one : Algebra.trace ℚ Em 1 = 2 := by
  rw [← map_one (algebraMap ℚ Em), Algebra.trace_algebraMap, finrank_Em]
  norm_num

theorem trace_ζ : Algebra.trace ℚ Em ζ = 0 := by
  have h := Algebra.trace_eq_of_algEquiv (cc.restrictScalars ℚ) ζ
  rw [AlgEquiv.restrictScalars_apply, cc_ζ, map_neg] at h
  linarith

theorem trace_rep (a b : ℚ) : Algebra.trace ℚ Em ((a : Em) + (b : Em) * ζ) = 2 * a := by
  have h1 : Algebra.trace ℚ Em (a : Em) = 2 * a := by
    rw [← eq_ratCast (algebraMap ℚ Em) a, Algebra.trace_algebraMap, finrank_Em, nsmul_eq_mul]
    norm_num
  have h2 : Algebra.trace ℚ Em ((b : Em) * ζ) = 0 := by
    rw [← eq_ratCast (algebraMap ℚ Em) b, ← Algebra.smul_def, map_smul, trace_ζ, smul_zero]
  rw [map_add, h1, h2, add_zero]

theorem qsmul_eq (q : ℚ) (v : Em) : q • v = (q : Em) * v := by
  rw [← eq_ratCast (algebraMap ℚ Em) q]
  exact Algebra.smul_def q v

theorem trace_of_integral {w : Em} (hw : IsIntegral ℤ w) : ∃ m : ℤ, Algebra.trace ℚ Em (ζ / 2 * w) = m := by
  obtain ⟨c, d, rfl⟩ := exists_int hw
  refine ⟨-d, ?_⟩
  have : ζ / 2 * ((c : Em) + (d : Em) * ζ) = (((-(d : ℚ) / 2 : ℚ)) : Em) + (((c : ℚ) / 2 : ℚ) : Em) * ζ := by
    push_cast
    linear_combination (d / 2 : Em) * ζ_sq
  rw [this, trace_rep]
  push_cast
  ring

theorem integral_of_trace {v : Em} (h1 : ∃ m : ℤ, Algebra.trace ℚ Em (ζ / 2 * v) = m)
    (h2 : ∃ m : ℤ, Algebra.trace ℚ Em (ζ / 2 * (v * ζ)) = m) : IsIntegral ℤ v := by
  obtain ⟨a, b, rfl⟩ := exists_rat v
  obtain ⟨m1, hm1⟩ := h1
  obtain ⟨m2, hm2⟩ := h2
  have e1 : ζ / 2 * ((a : Em) + (b : Em) * ζ) = (((-b / 2 : ℚ)) : Em) + (((a / 2 : ℚ)) : Em) * ζ := by
    push_cast
    linear_combination (b / 2 : Em) * ζ_sq
  have e2 : ζ / 2 * (((a : Em) + (b : Em) * ζ) * ζ) =
      (((-a / 2 : ℚ)) : Em) + (((-b / 2 : ℚ)) : Em) * ζ := by
    push_cast
    linear_combination (a / 2 + b / 2 * ζ : Em) * ζ_sq
  rw [e1, trace_rep] at hm1
  rw [e2, trace_rep] at hm2
  have hb : b = ((-m1 : ℤ) : ℚ) := by push_cast; linarith
  have ha : a = ((-m2 : ℤ) : ℚ) := by push_cast; linarith
  rw [ha, hb]
  have := isIntegral_rep (-m2) (-m1)
  simpa using this

def gaussH : Matrix (Fin 2) (Fin 2) Em := !![1, 0; 0, -1]

theorem hermForm_gauss (x y : Fin 2 → Em) :
    hermForm Em gaussH x y = cc (x 0) * y 0 - cc (x 1) * y 1 := by
  simp [hermForm, gaussH, Fin.sum_univ_two]
  ring

def gaussL : Submodule (𝓞 Em) (Fin 2 → Em) where
  carrier := {x | ∀ a, IsIntegral ℤ (x a)}
  add_mem' hx hy a := (hx a).add (hy a)
  zero_mem' _ := isIntegral_zero
  smul_mem' c x hx a := by
    show IsIntegral ℤ ((c • x) a)
    rw [Pi.smul_apply, Algebra.smul_def]
    exact (RingOfIntegers.isIntegral_coe c).mul (hx a)

theorem mem_gaussL {x : Fin 2 → Em} : x ∈ gaussL ↔ ∀ a, IsIntegral ℤ (x a) := Iff.rfl

theorem single_mem (a : Fin 2) {v : Em} (hv : IsIntegral ℤ v) : Pi.single a v ∈ gaussL := by
  intro b
  by_cases h : b = a
  · subst h; simpa using hv
  · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero

theorem gaussL_fg : (gaussL.restrictScalars ℤ).FG := by
  let f : (Fin 2 → 𝓞 Em) →ₗ[ℤ] (Fin 2 → Em) :=
    LinearMap.pi fun a => ((Algebra.linearMap (𝓞 Em) Em).restrictScalars ℤ).comp (LinearMap.proj a)
  have : gaussL.restrictScalars ℤ = Submodule.map f ⊤ := by
    ext x
    simp only [Submodule.restrictScalars_mem, Submodule.map_top, LinearMap.mem_range]
    constructor
    · intro hx
      exact ⟨fun a => ⟨x a, hx a⟩, by funext a; rfl⟩
    · rintro ⟨z, rfl⟩ a
      exact RingOfIntegers.isIntegral_coe (z a)
  rw [this]
  exact (Module.Finite.fg_top).map f

theorem gaussL_span : Submodule.span ℚ (gaussL : Set (Fin 2 → Em)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x => ?_
  obtain ⟨p0, q0, h0⟩ := exists_rat (x 0)
  obtain ⟨p1, q1, h1⟩ := exists_rat (x 1)
  have hx : x = p0 • (Pi.single 0 (1 : Em) : Fin 2 → Em) + q0 • (Pi.single 0 ζ : Fin 2 → Em) +
      (p1 • (Pi.single 1 (1 : Em) : Fin 2 → Em) + q1 • (Pi.single 1 ζ : Fin 2 → Em)) := by
    funext b
    fin_cases b
    · simp [h0, qsmul_eq]
    · simp [h1, qsmul_eq]
  have m : ∀ (a : Fin 2) (v : Em), IsIntegral ℤ v → Pi.single a v ∈ Submodule.span ℚ (gaussL : Set (Fin 2 → Em)) :=
    fun a v hv => Submodule.subset_span (single_mem a hv)
  rw [hx]
  exact add_mem (add_mem (Submodule.smul_mem _ _ (m 0 1 isIntegral_one))
    (Submodule.smul_mem _ _ (m 0 ζ ζ_isIntegral)))
    (add_mem (Submodule.smul_mem _ _ (m 1 1 isIntegral_one)) (Submodule.smul_mem _ _ (m 1 ζ ζ_isIntegral)))

theorem cc_isIntegral {v : Em} (hv : IsIntegral ℤ v) : IsIntegral ℤ (cc v) :=
  hv.map (cc : Em →+* Em).toIntAlgHom

theorem gauss_selfDual (x : Fin 2 → Em) :
    x ∈ gaussL ↔ ∀ y ∈ gaussL, ∃ m : ℤ, trForm Em (ζ / 2) gaussH x y = m := by
  constructor
  · intro hx y hy
    unfold trForm
    rw [hermForm_gauss]
    exact trace_of_integral (((cc_isIntegral (hx 0)).mul (hy 0)).sub ((cc_isIntegral (hx 1)).mul (hy 1)))
  · intro h
    have hv : ∀ (a : Fin 2) (v : Em), IsIntegral ℤ v → ∃ m : ℤ, trForm Em (ζ / 2) gaussH x (Pi.single a v) = m :=
      fun a v hv => h _ (single_mem a hv)
    have i0 : IsIntegral ℤ (cc (x 0)) := by
      refine integral_of_trace ?_ ?_
      · obtain ⟨m, hm⟩ := hv 0 1 isIntegral_one
        exact ⟨m, by simpa [trForm, hermForm_gauss] using hm⟩
      · obtain ⟨m, hm⟩ := hv 0 ζ ζ_isIntegral
        exact ⟨m, by simpa [trForm, hermForm_gauss] using hm⟩
    have i1 : IsIntegral ℤ (-cc (x 1)) := by
      refine integral_of_trace ?_ ?_
      · obtain ⟨m, hm⟩ := hv 1 1 isIntegral_one
        exact ⟨m, by simpa [trForm, hermForm_gauss] using hm⟩
      · obtain ⟨m, hm⟩ := hv 1 ζ ζ_isIntegral
        exact ⟨m, by simpa [trForm, hermForm_gauss, neg_mul] using hm⟩
    intro a
    fin_cases a
    · simpa using cc_isIntegral i0
    · simpa using cc_isIntegral i1.neg

theorem gauss_signature :
    (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * gaussH.map φ₀ * 1 = signMat 2 1 := by
  rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gaussH, signMat, Matrix.diagonal]

def gaussDatum : HermDatum Em Unit 2 1 where
  emb _ := φ₀
  emb_inj _ _ _ := rfl
  cmType := cmType
  H := gaussH
  herm a b := by
    fin_cases a <;> fin_cases b <;> simp [gaussH]
  ξ := ζ / 2
  ξ_ne := div_ne_zero (hζ.ne_zero (by norm_num)) two_ne_zero
  ξ_conj := by rw [map_div₀, cc_ζ, map_ofNat, neg_div]
  L := gaussL
  fg := gaussL_fg
  span := gaussL_span
  selfDual := gauss_selfDual
  signature _ := ⟨1, by simp, gauss_signature⟩
  level := 3
  three_le_level := le_rfl

end GroundTheory.Heights₂.Heights.NineStatements.Gauss
