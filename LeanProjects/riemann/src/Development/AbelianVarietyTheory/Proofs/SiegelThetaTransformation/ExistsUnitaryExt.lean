import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.RowExt

theorem exists_right_inv {E : Type} [Field E] [NumberField E] {κ ι : Type} [Fintype κ] [Fintype ι]
    [DecidableEq κ] (c : E) (W : Matrix κ ι E) (hW : IntM W)
    (hli : LinearIndependent E (fun i => W i))
    (hprim : ∀ t : κ → E, (∀ j, IsIntegral ℤ ((t ᵥ* W) j)) → ∀ i, IsIntegral ℤ (c * t i)) :
    ∃ X : Matrix ι κ E, IntM X ∧ W * X = c • (1 : Matrix κ κ E) := by
  classical
  have hinj : LinearMap.ker W.vecMulLinear = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Matrix.vecMul_injective_iff.mpr hli
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  have hg' : ∀ t, g (t ᵥ* W) = t := fun t => LinearMap.congr_fun hg t
  let j : (ι → 𝓞 E) →ₗ[𝓞 E] (ι → E) := (Algebra.linearMap (𝓞 E) E).compLeft ι
  let q : (ι → E) →ₗ[E] (ι → E) := LinearMap.id - W.vecMulLinear ∘ₗ g
  let φ : (ι → 𝓞 E) →ₗ[𝓞 E] (ι → E) := (q.restrictScalars (𝓞 E)) ∘ₗ j
  haveI : Module.Finite (𝓞 E) (LinearMap.range φ) := inferInstance
  haveI : Module.FinitePresentation (𝓞 E) (LinearMap.range φ) :=
    Module.finitePresentation_of_finite _ _
  haveI : Module.Flat (𝓞 E) (LinearMap.range φ) := inferInstance
  haveI : Module.Projective (𝓞 E) (LinearMap.range φ) :=
    Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property φ.rangeRestrict LinearMap.id
    φ.surjective_rangeRestrict
  let r : (ι → 𝓞 E) →ₗ[𝓞 E] (ι → 𝓞 E) := LinearMap.id - s ∘ₗ φ.rangeRestrict
  have hr : ∀ m, φ (r m) = 0 := by
    intro m
    have := congrArg Subtype.val (LinearMap.congr_fun hs (φ.rangeRestrict m))
    simp only [r, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
    rw [sub_eq_zero]
    exact this.symm
  have hr' : ∀ m, g (j (r m)) ᵥ* W = j (r m) := by
    intro m
    have : j (r m) - g (j (r m)) ᵥ* W = 0 := hr m
    exact (sub_eq_zero.mp this).symm
  let h : (ι → 𝓞 E) →ₗ[𝓞 E] (κ → E) := (g.restrictScalars (𝓞 E)) ∘ₗ j ∘ₗ r
  refine ⟨Matrix.of fun a k => c * h (Pi.single a 1) k, ?_, ?_⟩
  · intro a k
    refine hprim _ (fun b => ?_) k
    show IsIntegral ℤ ((g (j (r _)) ᵥ* W) b)
    rw [hr']
    exact RingOfIntegers.isIntegral_coe _
  · ext i k
    let w : ι → 𝓞 E := fun a => ⟨W i a, hW i a⟩
    have hjw : j w = Pi.single i 1 ᵥ* W := by
      rw [Matrix.single_one_vecMul]; rfl
    have hφw : φ.rangeRestrict w = 0 := by
      apply Subtype.ext
      show j w - g (j w) ᵥ* W = 0
      rw [hjw, hg', sub_self]
    have hw : h w = Pi.single i 1 := by
      show g (j (w - s (φ.rangeRestrict w))) = _
      rw [hφw, map_zero, sub_zero, hjw, hg']
    have hw2 : w = ∑ a, w a • Pi.single a 1 := pi_eq_sum_univ' w
    rw [hw2, map_sum] at hw
    have := congrFun hw k
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply] at this
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    have h1 : (1 : Matrix κ κ E) i k = (Pi.single i 1 : κ → E) k := by
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [h1, ← this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, mul_left_comm]
    rfl

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {α β γ : Type}

theorem ccT_eq (A : Matrix α β E) : ccT A = Aᴴ := rfl

omit [NumberField E] [IsCMField E] in
theorem intM_mul [Fintype β] {A : Matrix α β E} {B : Matrix β γ E} (hA : IntM A) (hB : IntM B) :
    IntM (A * B) := fun a c => by
  rw [Matrix.mul_apply]
  exact IsIntegral.sum _ fun b _ => (hA a b).mul (hB b c)

theorem intM_conj {A : Matrix α β E} (hA : IntM A) : IntM Aᴴ := fun a b =>
  (hA b a).map ((IsCMField.complexConj E).toAlgHom.restrictScalars ℤ)

omit [NumberField E] [IsCMField E] in
theorem intM_nat {A : Matrix α β E} (n : ℕ) (hA : IntM A) : IntM ((n : E) • A) := fun a b =>
  (isIntegral_natCast n).mul (hA a b)

omit [NumberField E] [IsCMField E] in
theorem intM_J [DecidableEq α] : IntM (Matrix.J α E) := by
  rintro (a | a) (b | b) <;> by_cases h : a = b <;>
    simp [Matrix.J, Matrix.one_apply, h, isIntegral_zero, isIntegral_one, isIntegral_one.neg]

theorem J_conj [DecidableEq α] : (Matrix.J α E)ᴴ = -Matrix.J α E := by
  simp [Matrix.J, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]

end

theorem exists_unitary_ext :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N c : ℕ), 0 < c → ∃ c' : ℕ, 0 < c' ∧
      ∀ W : Matrix (Fin N) (Fin N ⊕ Fin N) E, IntM W → LinearIndependent E (fun i => W i) →
        W * Matrix.J (Fin N) E * ccT W = 0 →
        (∀ t : Fin N → E, (∀ j, IsIntegral ℤ ((t ᵥ* W) j)) → ∀ i, IsIntegral ℤ ((c : E) * t i)) →
        ∃ γ ∈ UU E N, Den c' γ ∧ ∀ a, γ (Sum.inr a) = W a := by
  intro E _ _ _ N c hc
  refine ⟨2 * c * c, by positivity, fun W hW hli hiso hprim => ?_⟩
  obtain ⟨X, hX, hWX⟩ := exists_right_inv (c : E) W hW hli hprim
  rw [ccT_eq] at hiso
  have hc0 : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  set J := Matrix.J (Fin N) E with hJ
  have hJJ : J * J = -1 := Matrix.J_squared _ _
  have hJc : Jᴴ = -J := J_conj
  have hJi : IntM J := intM_J
  obtain ⟨V₀, hV₀⟩ : ∃ V₀ : Matrix (Fin N) (Fin N ⊕ Fin N) E, V₀ = (c : E)⁻¹ • (Xᴴ * J) := ⟨_, rfl⟩
  have hcV : (c : E) • V₀ = Xᴴ * J := by rw [hV₀, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have hVi : IntM ((c : E) • V₀) := hcV ▸ intM_mul (intM_conj hX) hJi
  have h1 : V₀ * J * Wᴴ = -1 := by
    rw [hV₀, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc Xᴴ, hJJ, Matrix.mul_neg,
      Matrix.mul_one, Matrix.neg_mul, ← Matrix.conjTranspose_mul, hWX]
    simp [smul_smul, hc0]
  have skew : ∀ A B : Matrix (Fin N) (Fin N ⊕ Fin N) E, (A * J * Bᴴ)ᴴ = -(B * J * Aᴴ) := by
    intro A B
    simp [Matrix.conjTranspose_mul, hJc, Matrix.mul_assoc]
  have h2 : W * J * V₀ᴴ = 1 := by
    have := skew V₀ W
    rw [h1] at this
    simpa using this.symm
  obtain ⟨S, hS⟩ : ∃ S, S = V₀ * J * V₀ᴴ := ⟨_, rfl⟩
  have hSc : Sᴴ = -S := hS ▸ skew V₀ V₀
  obtain ⟨T, hT⟩ : ∃ T, T = (-(2 : E)⁻¹) • S := ⟨_, rfl⟩
  have hTc : Tᴴ = -T := by
    rw [hT, Matrix.conjTranspose_smul, hSc]; simp
  obtain ⟨V, hV⟩ : ∃ V, V = V₀ + T * W := ⟨_, rfl⟩
  have k2 : W * J * Vᴴ = 1 := by
    rw [hV, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.mul_add, h2,
      ← Matrix.mul_assoc, hiso, Matrix.zero_mul, add_zero]
  have k1 : V * J * Wᴴ = -1 := by
    have := skew W V
    rw [k2] at this
    rw [← neg_neg (V * J * Wᴴ), ← this]; simp
  have k0 : V * J * Vᴴ = 0 := by
    have e : V * J * V₀ᴴ = S + T := by
      rw [hV, Matrix.add_mul, Matrix.add_mul, ← hS, Matrix.mul_assoc T, Matrix.mul_assoc T, h2,
        Matrix.mul_one]
    conv_lhs => rw [show Vᴴ = V₀ᴴ + Wᴴ * Tᴴ by
      rw [hV, Matrix.conjTranspose_add, Matrix.conjTranspose_mul]]
    rw [Matrix.mul_add, e, ← Matrix.mul_assoc, k1, hTc, hT]
    simp only [Matrix.neg_mul, Matrix.one_mul, neg_neg]
    rw [add_assoc, ← add_smul, show (-(2 : E)⁻¹ + -(2 : E)⁻¹) = -1 by norm_num]
    simp
  have key : Matrix.fromRows V W * J * (Matrix.fromRows V W)ᴴ = J := by
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols, k0, k1, k2, hiso]
    rfl
  refine ⟨Matrix.fromRows V W, ?_, ?_, fun a => rfl⟩
  · generalize Matrix.fromRows V W = g at key
    show gᴴ * J * g = J
    have e1 : g * (J * gᴴ * -J) = 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, key, Matrix.mul_neg, hJJ, neg_neg]
    have e2 := mul_eq_one_comm.mp e1
    have e3 : J * (J * gᴴ * -J * g) = J := by rw [e2, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ] at e3
    simpa using e3
  · have hVV : ((2 * c * c : ℕ) : E) • V = ((2 * c : ℕ) : E) • ((c : E) • V₀) -
        ((c : E) • V₀) * J * ((c : E) • V₀)ᴴ * W := by
      rw [hV, hT, hS]
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
        star_natCast, sub_eq_add_neg, ← neg_smul]
      congr 2
      · push_cast; ring
      · push_cast; field_simp
    have i1 := intM_nat (2 * c) hVi
    have i2 := intM_mul (intM_mul (intM_mul hVi hJi) (intM_conj hVi)) hW
    rintro (a | a) b
    · show IsIntegral ℤ ((((2 * c * c : ℕ) : E) • V) a b)
      rw [hVV]
      exact (i1 a b).sub (i2 a b)
    · exact intM_nat (2 * c * c) hW a b

end GlobalTheory.SW.RowExt
