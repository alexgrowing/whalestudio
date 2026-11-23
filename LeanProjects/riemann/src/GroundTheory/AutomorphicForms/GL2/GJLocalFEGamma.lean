import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJLocalFECoeff
import GroundTheory.AutomorphicForms.WhittakerCriterion

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic MeasureTheory Measures GJMatrix Polynomial
open scoped NNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

variable (F) in

def IsGammaFactor (π : Representation ℂ (GL (Fin n) F) V) (μ : Measure (GL (Fin n) F))
    (ψ : AddChar F Circle) (γ : RatFunc ℂ) : Prop :=
  ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ → ∀ v : V,
    ∀ ℓ ∈ smoothVectors (Representation.dual π),
      RatFE F γ (zetaIntegral μ Φ (matrixCoeff π v ℓ))
        (fun s => zetaIntegral μ (localMatrixFourier ψ Φ) (fun g => matrixCoeff π v ℓ g⁻¹) (1 - s))

omit [BorelSpace (GL (Fin n) F)] in

theorem IsGammaFactor.smul_measure {μ : Measure (GL (Fin n) F)} {ψ : AddChar F Circle}
    {γ : RatFunc ℂ} (h : IsGammaFactor F π μ ψ γ) (c : ℝ≥0) : IsGammaFactor F π (c • μ) ψ γ := by
  intro Φ hΦ v ℓ hℓ
  refine ((h Φ hΦ v ℓ hℓ).const_mul ((c : ℝ) : ℂ)).congr ⟨0, fun s _ => ?_⟩ ⟨0, fun s _ => ?_⟩
  · rw [zetaIntegral, zetaIntegral, integral_smul_nnreal_measure, NNReal.smul_def,
      Complex.real_smul]
  · rw [zetaIntegral, zetaIntegral, integral_smul_nnreal_measure, NNReal.smul_def,
      Complex.real_smul]

theorem IsGammaFactor.of_isHaarMeasure {μ ν : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]
    [ν.IsHaarMeasure] {ψ : AddChar F Circle} {γ : RatFunc ℂ} (h : IsGammaFactor F π μ ψ γ) :
    IsGammaFactor F π ν ψ γ := by
  rw [Measure.isMulLeftInvariant_eq_smul ν μ]
  exact h.smul_measure _

theorem IsGammaFactor.unique [π.IsIrreducible] (hπ : IsAdmissible π) {μ : Measure (GL (Fin n) F)}
    [μ.IsHaarMeasure] {ψ : AddChar F Circle} {γ γ' : RatFunc ℂ} (h : IsGammaFactor F π μ ψ γ)
    (h' : IsGammaFactor F π μ ψ γ') : γ = γ' := by
  classical
  obtain ⟨v₀, hv₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have : Nontrivial V := ⟨⟨v₀, 0, hv₀⟩⟩
  have h1 := one_mem_zetaIdeal μ hπ.1 (π := π)
  obtain ⟨R, hR, hR0⟩ : ∃ R ∈ zetaSet π μ, R ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hbot : zetaIdeal π μ = ⊥ := Submodule.span_eq_bot.2 hcon
    rw [hbot, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  obtain ⟨Φ, v, ℓ, hΦ, hℓ, s₀, hZ⟩ := hR
  refine RatFE.unique (h Φ hΦ v ℓ hℓ) (h' Φ hΦ v ℓ hℓ) fun t => ?_
  by_contra hcon
  push Not at hcon
  apply hR0
  refine eq_of_eval_qs_eq_right (F := F) (s₁ := max t s₀) fun s hs => ?_
  rw [max_lt_iff] at hs
  rw [← hZ s hs.2, hcon s hs.1, RatFunc.eval_zero]

variable (F π) in

def gammaFactor (ψ : AddChar F Circle) : RatFunc ℂ := by
  classical
  exact if h : ∃ γ : RatFunc ℂ, IsGammaFactor F π (Measure.haar : Measure (GL (Fin n) F)) ψ γ
    then h.choose else 0

theorem isGammaFactor_gammaFactor [π.IsIrreducible] (hπ : IsAdmissible π)
    {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure] {ψ : AddChar F Circle} {γ : RatFunc ℂ}
    (hγ : IsGammaFactor F π μ ψ γ) : IsGammaFactor F π μ ψ (gammaFactor F π ψ) := by
  classical
  have hH : IsGammaFactor F π (Measure.haar : Measure (GL (Fin n) F)) ψ γ :=
    hγ.of_isHaarMeasure
  have hex : ∃ γ : RatFunc ℂ, IsGammaFactor F π (Measure.haar : Measure (GL (Fin n) F)) ψ γ :=
    ⟨γ, hH⟩
  have hg : gammaFactor F π ψ = γ := by
    rw [gammaFactor, dif_pos hex]
    exact IsGammaFactor.unique hπ hex.choose_spec hH
  rw [hg]
  exact hγ

theorem functionalEquation_of_inducedFE [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1)
    (hI : ∀ (β : Fin n → ℕ) (W : Type u) [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ (levi F n β) W), IsAdmissible σ → σ.IsIrreducible → IsCuspidal σ →
        ∃ γ, InducedFE F σ μ ψ γ) :
    ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ → ∀ v : V,
      ∀ ℓ ∈ smoothVectors (Representation.dual π),
        (∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → Integrable (fun g : GL (Fin n) F =>
          Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g *
            detPow g (s + ((n : ℂ) - 1) / 2)) μ) ∧
        (∃ s₁ : ℝ, ∀ s : ℂ, s.re < s₁ → Integrable (fun g : GL (Fin n) F =>
          localMatrixFourier ψ Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g⁻¹ *
            detPow g ((1 - s) + ((n : ℂ) - 1) / 2)) μ) ∧
        RatFE F (gammaFactor F π ψ) (zetaIntegral μ Φ (matrixCoeff π v ℓ))
          (fun s => zetaIntegral μ (localMatrixFourier ψ Φ) (fun g => matrixCoeff π v ℓ g⁻¹)
            (1 - s)) := by
  obtain ⟨γ, hγ⟩ := exists_coeffFE_of_inducedFE hπ μ hψ hψ1 hI
  have hG : IsGammaFactor F π μ ψ γ := fun Φ hΦ v ℓ hℓ => (hγ Φ hΦ v ℓ hℓ).2.2
  have heq : gammaFactor F π ψ = γ := IsGammaFactor.unique hπ (isGammaFactor_gammaFactor hπ hG) hG
  intro Φ hΦ v ℓ hℓ
  rw [heq]
  exact hγ Φ hΦ v ℓ hℓ

theorem isGammaFactor_gammaFactor_of_inducedFE [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1)
    (hI : ∀ (β : Fin n → ℕ) (W : Type u) [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ (levi F n β) W), IsAdmissible σ → σ.IsIrreducible → IsCuspidal σ →
        ∃ γ, InducedFE F σ μ ψ γ) :
    IsGammaFactor F π μ ψ (gammaFactor F π ψ) := fun Φ hΦ v ℓ hℓ =>
  (functionalEquation_of_inducedFE hπ μ hψ hψ1 hI Φ hΦ v ℓ hℓ).2.2

theorem existsUnique_isGammaFactor_of_inducedFE [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1)
    (hI : ∀ (β : Fin n → ℕ) (W : Type u) [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ (levi F n β) W), IsAdmissible σ → σ.IsIrreducible → IsCuspidal σ →
        ∃ γ, InducedFE F σ μ ψ γ) :
    ∃! γ : RatFunc ℂ, IsGammaFactor F π μ ψ γ :=
  ⟨gammaFactor F π ψ, isGammaFactor_gammaFactor_of_inducedFE hπ μ hψ hψ1 hI, fun _ h =>
    IsGammaFactor.unique hπ h (isGammaFactor_gammaFactor_of_inducedFE hπ μ hψ hψ1 hI)⟩

variable (F) in

abbrev qInv : ℂ := ((LocalField.residueCard F : ℂ))⁻¹

omit [MeasurableSpace F] [BorelSpace F] in
theorem qInv_ne_zero : qInv F ≠ 0 :=
  inv_ne_zero (Nat.cast_ne_zero.2 LocalField.residueCard_ne_zero)

omit [MeasurableSpace F] [BorelSpace F] in

theorem qs_one_sub (s : ℂ) : qs F (1 - s) = qInv F / qs F s := by
  have h1 : qs F (1 - s) * qs F s = qs F 1 := by rw [← qs_add, sub_add_cancel]
  have h2 : qs F 1 = qInv F := by rw [qs, Complex.cpow_neg_one]
  rw [eq_div_iff (qs_ne_zero s), h1, h2]

variable (F) in

def dualVar : RatFunc ℂ := RatFunc.C (qInv F) * RatFunc.X⁻¹

variable (F) in

def dualPoly (p : ℂ[X]) : ℂ[X] :=
  ∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i * qInv F ^ i) * X ^ (p.natDegree - i)

omit [MeasurableSpace F] [BorelSpace F] in
theorem eval_dualPoly (p : ℂ[X]) {x : ℂ} (hx : x ≠ 0) :
    (dualPoly F p).eval x = x ^ p.natDegree * p.eval (qInv F / x) := by
  rw [dualPoly, eval_finsetSum, eval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hpow : x ^ p.natDegree = x ^ (p.natDegree - i) * x ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [eval_mul, eval_C, eval_pow, eval_X, hpow, div_pow]
  field_simp

omit [MeasurableSpace F] [BorelSpace F] in
theorem aeval_dualVar (p : ℂ[X]) :
    aeval (dualVar F) p = algebraMap ℂ[X] (RatFunc ℂ) (dualPoly F p) /
      algebraMap ℂ[X] (RatFunc ℂ) (X ^ p.natDegree) := by
  have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  rw [aeval_eq_sum_range, dualPoly, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hpow : (RatFunc.X : RatFunc ℂ) ^ p.natDegree =
      RatFunc.X ^ (p.natDegree - i) * RatFunc.X ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [dualVar, map_mul, map_pow, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X, hpow,
    Algebra.smul_def, RatFunc.algebraMap_eq_C, map_mul, map_pow, mul_pow, inv_pow]
  field_simp

omit [MeasurableSpace F] [BorelSpace F] in
theorem aeval_dualVar_ne_zero {p : ℂ[X]} (hp : p ≠ 0) : aeval (dualVar F) p ≠ 0 := by
  rw [aeval_dualVar]
  refine div_ne_zero ?_ ?_
  · rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))]
    intro h0
    apply hp
    refine Polynomial.eq_zero_of_infinite_isRoot p
      ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono fun y hy => ?_)
    have hy0 : y ≠ 0 := hy
    have hx : qInv F / y ≠ 0 := div_ne_zero (qInv_ne_zero) hy0
    have := eval_dualPoly (F := F) p hx
    rw [h0, eval_zero, div_div_cancel₀ (qInv_ne_zero)] at this
    exact (mul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ hx)
  · rw [map_pow, RatFunc.algebraMap_X]
    exact pow_ne_zero _ RatFunc.X_ne_zero

variable (F) in

def dualSubst : RatFunc ℂ →ₐ[ℂ] RatFunc ℂ :=
  RatFunc.liftAlgHom (aeval (dualVar F)) fun _ hp =>
    mem_nonZeroDivisors_of_ne_zero (aeval_dualVar_ne_zero (nonZeroDivisors.ne_zero hp))

omit [MeasurableSpace F] [BorelSpace F] in
theorem dualSubst_algebraMap (p : ℂ[X]) :
    dualSubst F (algebraMap ℂ[X] (RatFunc ℂ) p) = aeval (dualVar F) p := by
  have := RatFunc.liftAlgHom_apply_div (φ := aeval (dualVar F)) (hφ := fun _ hp =>
    mem_nonZeroDivisors_of_ne_zero (aeval_dualVar_ne_zero (nonZeroDivisors.ne_zero hp))) p 1
  rw [map_one, div_one, map_one, div_one] at this
  exact this

omit [MeasurableSpace F] [BorelSpace F] in
theorem dualSubst_apply (R : RatFunc ℂ) :
    dualSubst F R = aeval (dualVar F) R.num / aeval (dualVar F) R.denom :=
  RatFunc.liftAlgHom_apply _ _ R

omit [MeasurableSpace F] [BorelSpace F] in

theorem eval_dualSubst (R : RatFunc ℂ) {x : ℂ} (hx : x ≠ 0)
    (hR : R.denom.eval (qInv F / x) ≠ 0) :
    (dualSubst F R).eval (RingHom.id ℂ) x = R.eval (RingHom.id ℂ) (qInv F / x) := by
  have h1 : algebraMap ℂ[X] (RatFunc ℂ) (X ^ R.num.natDegree) ≠ 0 := by
    rw [map_pow, RatFunc.algebraMap_X]; exact pow_ne_zero _ RatFunc.X_ne_zero
  have h2 : algebraMap ℂ[X] (RatFunc ℂ) (X ^ R.denom.natDegree) ≠ 0 := by
    rw [map_pow, RatFunc.algebraMap_X]; exact pow_ne_zero _ RatFunc.X_ne_zero
  have h3 : algebraMap ℂ[X] (RatFunc ℂ) (dualPoly F R.denom) ≠ 0 := by
    have := aeval_dualVar_ne_zero (F := F) R.denom_ne_zero
    intro h
    apply this
    rw [aeval_dualVar, h, zero_div]
  have hθ : dualSubst F R = algebraMap ℂ[X] (RatFunc ℂ) (dualPoly F R.num * X ^ R.denom.natDegree) /
      algebraMap ℂ[X] (RatFunc ℂ) (dualPoly F R.denom * X ^ R.num.natDegree) := by
    rw [dualSubst_apply, aeval_dualVar, aeval_dualVar, map_mul, map_mul]
    field_simp
  have hden : (dualPoly F R.denom * X ^ R.num.natDegree).eval x ≠ 0 := by
    rw [eval_mul, eval_pow, eval_X, eval_dualPoly _ hx]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hx) hR) (pow_ne_zero _ hx)
  rw [hθ, eval_div_algebraMap _ _ hden, eval_mul, eval_mul, eval_pow, eval_pow, eval_X,
    eval_dualPoly _ hx, eval_dualPoly _ hx]
  simp only [RatFunc.eval, eval₂_id]
  field_simp

omit [MeasurableSpace F] [BorelSpace F] in

theorem dualSubst_mem_laurentSubalgebra {L : RatFunc ℂ} (hL : L ∈ laurentSubalgebra) :
    dualSubst F L ∈ laurentSubalgebra := by
  have hX : dualSubst F RatFunc.X = dualVar F := by
    rw [← RatFunc.algebraMap_X, dualSubst_algebraMap, aeval_X]
  have hle : laurentSubalgebra ≤ (laurentSubalgebra).comap (dualSubst F) := by
    rw [laurentSubalgebra, Algebra.adjoin_le_iff]
    rintro y (rfl | rfl)
    · rw [SetLike.mem_coe, Subalgebra.mem_comap, hX, dualVar]
      exact mul_mem (C_mem_laurentSubalgebra _) X_inv_mem_laurentSubalgebra
    · rw [SetLike.mem_coe, Subalgebra.mem_comap, map_inv₀, hX, dualVar, mul_inv, inv_inv,
        ← map_inv₀]
      exact mul_mem (C_mem_laurentSubalgebra _) X_mem_laurentSubalgebra
  exact hle hL

omit [MeasurableSpace F] [BorelSpace F] in

theorem exists_eq_C_mul_X_pow_of_mem {ε : RatFunc ℂ} (h : ε ∈ laurentSubalgebra)
    (h' : ε⁻¹ ∈ laurentSubalgebra) (hε : ε ≠ 0) :
    ∃ (r : ℂ) (i a : ℕ), r ≠ 0 ∧
      ε = algebraMap ℂ[X] (RatFunc ℂ) (C r * X ^ i) / algebraMap ℂ[X] (RatFunc ℂ) (X ^ a) := by
  obtain ⟨P₁, a, h1⟩ := mem_laurentSubalgebra_iff.1 h
  obtain ⟨P₂, b, h2⟩ := mem_laurentSubalgebra_iff.1 h'
  have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have e1 : algebraMap ℂ[X] (RatFunc ℂ) P₁ = ε * RatFunc.X ^ a := by
    rw [h1, div_mul_cancel₀ _ (pow_ne_zero _ hX)]
  have e2 : algebraMap ℂ[X] (RatFunc ℂ) P₂ = ε⁻¹ * RatFunc.X ^ b := by
    rw [h2, div_mul_cancel₀ _ (pow_ne_zero _ hX)]
  have hprod : P₁ * P₂ = X ^ (a + b) := by
    apply IsFractionRing.injective ℂ[X] (RatFunc ℂ)
    rw [map_mul, e1, e2, map_pow, RatFunc.algebraMap_X, pow_add]
    field_simp
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow Polynomial.prime_X (a + b)).1 ⟨P₂, hprod.symm⟩
  obtain ⟨u, hu⟩ := hi
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.1 (u⁻¹).isUnit
  have hP₁ : P₁ = C r * X ^ i := by
    rw [hru, ← hu, mul_comm P₁ (u : ℂ[X]), ← mul_assoc, Units.inv_mul, one_mul]
  exact ⟨r, i, a, hr.ne_zero, by rw [h1, hP₁, map_pow, RatFunc.algebraMap_X]⟩

section Contragredient

variable [π.IsIrreducible] (hπ : IsAdmissible π) {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]
  {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {γ : RatFunc ℂ}
  (hγ : IsGammaFactor F π μ ψ γ)
include hπ hψ hψ1 hγ

theorem exists_mem_zetaSet_contragredient {R : RatFunc ℂ} (hR : R ∈ zetaSet π μ) :
    ∃ R' ∈ zetaSet (contragredient π) μ, γ * R = dualSubst F R' := by
  have := Whittaker.isIrreducible_contragredient hπ
  have hπ' := isAdmissible_contragredient hπ
  obtain ⟨Φ, v, ℓ, hΦ, hℓ, s₀, hZ⟩ := hR
  obtain ⟨R₁, s₁, hA, hB⟩ := hγ Φ hΦ v ℓ hℓ
  have hR₁ : R₁ = R := eq_of_eval_qs_eq_right (F := F) (s₁ := max s₀ s₁) fun s hs => by
    rw [max_lt_iff] at hs
    rw [← hA s hs.2, hZ s hs.1]
  subst hR₁
  have hΦh := hΦ.localMatrixFourier hψ hψ1
  obtain ⟨s₂, hrat⟩ := exists_ratFunc_zetaIntegral (π := contragredient π) hπ' μ
  obtain ⟨R', hR'⟩ := hrat _ hΦh ⟨ℓ, hℓ⟩ (evalSmooth π v) (evalSmooth_mem (hπ.1 v))
  refine ⟨R', ⟨_, ⟨ℓ, hℓ⟩, evalSmooth π v, hΦh, evalSmooth_mem (hπ.1 v), s₂, hR'⟩, ?_⟩
  obtain ⟨t, ht⟩ := exists_denom_ne_zero_right (F := F) R'
  refine eq_of_eval_qs_eq_left (F := F) (s₁ := min (-s₁) (min (1 - s₂) (1 - t))) fun s hs => ?_
  simp only [lt_min_iff] at hs
  have h1 : s₂ < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have h2 : t < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  rw [← hB s hs.1, eval_dualSubst R' (qs_ne_zero s) (by rw [← qs_one_sub]; exact ht _ h2),
    ← qs_one_sub, ← hR' _ h1]
  rfl

theorem exists_mem_zetaSet_of_contragredient {R' : RatFunc ℂ}
    (hR' : R' ∈ zetaSet (contragredient π) μ) :
    ∃ R ∈ zetaSet π μ, dualSubst F R' = γ * R := by
  obtain ⟨Φ', x, Λ, hΦ', hΛ, s₀, hZ'⟩ := hR'
  obtain ⟨v, hv⟩ := (toDoubleContragredient_bijective hπ).2 ⟨Λ, hΛ⟩
  have hΛv : Λ = evalSmooth π v := (congrArg Subtype.val hv).symm
  subst hΛv
  obtain ⟨Φ, hΦ, rfl⟩ := exists_localMatrixFourier_eq hψ hψ1 hΦ'
  obtain ⟨s₂, hrat⟩ := exists_ratFunc_zetaIntegral hπ μ
  obtain ⟨R, hR⟩ := hrat Φ hΦ v x.1 x.2
  refine ⟨R, ⟨Φ, v, x.1, hΦ, x.2, s₂, hR⟩, ?_⟩
  obtain ⟨R₁, s₁, hA, hB⟩ := hγ Φ hΦ v x.1 x.2
  have hR₁ : R₁ = R := eq_of_eval_qs_eq_right (F := F) (s₁ := max s₂ s₁) fun s hs => by
    rw [max_lt_iff] at hs
    rw [← hA s hs.2, hR s hs.1]
  subst hR₁
  obtain ⟨t, ht⟩ := exists_denom_ne_zero_right (F := F) R'
  refine eq_of_eval_qs_eq_left (F := F) (s₁ := min (-s₁) (min (1 - s₀) (1 - t))) fun s hs => ?_
  simp only [lt_min_iff] at hs
  have h1 : s₀ < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have h2 : t < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  rw [eval_dualSubst R' (qs_ne_zero s) (by rw [← qs_one_sub]; exact ht _ h2), ← qs_one_sub,
    ← hZ' _ h1, ← hB s hs.1]
  rfl

theorem exists_mem_zetaIdeal_contragredient {R : RatFunc ℂ} (hR : R ∈ zetaIdeal π μ) :
    ∃ R' ∈ zetaIdeal (contragredient π) μ, γ * R = dualSubst F R' := by
  induction hR using Submodule.span_induction with
  | mem R hR =>
    obtain ⟨R', hR', h⟩ := exists_mem_zetaSet_contragredient hπ hψ hψ1 hγ hR
    exact ⟨R', Submodule.subset_span hR', h⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add R₁ R₂ _ _ h₁ h₂ =>
    obtain ⟨R'₁, hm₁, e₁⟩ := h₁
    obtain ⟨R'₂, hm₂, e₂⟩ := h₂
    exact ⟨R'₁ + R'₂, add_mem hm₁ hm₂, by rw [mul_add, e₁, e₂, map_add]⟩
  | smul c R _ h =>
    obtain ⟨R', hm, e⟩ := h
    refine ⟨c • R', Submodule.smul_mem _ c hm, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes, ← e]
    ring

theorem exists_mem_zetaIdeal_of_contragredient {R' : RatFunc ℂ}
    (hR' : R' ∈ zetaIdeal (contragredient π) μ) :
    ∃ R ∈ zetaIdeal π μ, dualSubst F R' = γ * R := by
  induction hR' using Submodule.span_induction with
  | mem R' hR' =>
    obtain ⟨R, hR, h⟩ := exists_mem_zetaSet_of_contragredient hπ hψ hψ1 hγ hR'
    exact ⟨R, Submodule.subset_span hR, h⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add R₁ R₂ _ _ h₁ h₂ =>
    obtain ⟨S₁, hm₁, e₁⟩ := h₁
    obtain ⟨S₂, hm₂, e₂⟩ := h₂
    exact ⟨S₁ + S₂, add_mem hm₁ hm₂, by rw [map_add, e₁, e₂, mul_add]⟩
  | smul c R' _ h =>
    obtain ⟨S, hm, e⟩ := h
    refine ⟨c • S, Submodule.smul_mem _ c hm, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes, e]
    ring

end Contragredient

variable (F π) in

def epsilonFactor (ψ : AddChar F Circle) : RatFunc ℂ :=
  gammaFactor F π ψ *
    dualSubst F (algebraMap ℂ[X] (RatFunc ℂ) (LPolynomial (contragredient π))) /
      algebraMap ℂ[X] (RatFunc ℂ) (LPolynomial π)

theorem exists_epsilonFactor_eq_of_inducedFE [NeZero n] [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1)
    (hI : ∀ (β : Fin n → ℕ) (W : Type u) [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ (levi F n β) W), IsAdmissible σ → σ.IsIrreducible → IsCuspidal σ →
        ∃ γ, InducedFE F σ μ ψ γ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ k : ℤ, epsilonFactor F π ψ = RatFunc.C c * RatFunc.X ^ k ∧
      ∀ s : ℂ, (LPolynomial π).eval (qs F s) ≠ 0 →
        (LPolynomial (contragredient π)).eval (qs F (1 - s)) ≠ 0 →
          (gammaFactor F π ψ).eval (RingHom.id ℂ) (qs F s) * LFunction π s /
            LFunction (contragredient π) (1 - s) = c * qs F s ^ k := by
  have hγ := isGammaFactor_gammaFactor_of_inducedFE hπ μ hψ hψ1 hI
  have := Whittaker.isIrreducible_contragredient hπ
  have hπ' := isAdmissible_contragredient hπ
  obtain ⟨hP0, hP⟩ := LPolynomial_spec hπ μ
  obtain ⟨hP'0, hP'⟩ := LPolynomial_spec hπ' μ
  have hPpoly : LPolynomial π ≠ 0 := fun h => by
    rw [h, eval_zero] at hP0
    exact zero_ne_one hP0
  have hP'poly : LPolynomial (contragredient π) ≠ 0 := fun h => by
    rw [h, eval_zero] at hP'0
    exact zero_ne_one hP'0
  have hPne : algebraMap ℂ[X] (RatFunc ℂ) (LPolynomial π) ≠ 0 := RatFunc.algebraMap_ne_zero hPpoly
  have hθne : dualSubst F (algebraMap ℂ[X] (RatFunc ℂ) (LPolynomial (contragredient π))) ≠ 0 := by
    rw [dualSubst_algebraMap]
    exact aeval_dualVar_ne_zero hP'poly

  obtain ⟨R', hR'mem, hR'⟩ := exists_mem_zetaIdeal_contragredient hπ hψ hψ1 hγ
    ((hP _).2 ⟨1, one_mem _, rfl⟩)
  obtain ⟨L₁, hL₁, rfl⟩ := (hP' R').1 hR'mem
  have hε1 : epsilonFactor F π ψ = dualSubst F L₁ := by
    rw [map_div₀] at hR'
    rw [epsilonFactor]
    field_simp
    field_simp at hR'
    rw [hR']

  obtain ⟨R, hRmem, hR⟩ := exists_mem_zetaIdeal_of_contragredient hπ hψ hψ1 hγ
    ((hP' _).2 ⟨1, one_mem _, rfl⟩)
  obtain ⟨L₂, hL₂, rfl⟩ := (hP R).1 hRmem
  have hγne : gammaFactor F π ψ ≠ 0 := by
    intro h0
    rw [h0, zero_mul, map_div₀, map_one] at hR
    exact one_div_ne_zero hθne hR
  have hε2 : (epsilonFactor F π ψ)⁻¹ = L₂ := by
    rw [map_div₀, map_one] at hR
    rw [epsilonFactor]
    field_simp
    field_simp at hR
    rw [hR]
    ring
  have hεne : epsilonFactor F π ψ ≠ 0 := by
    rw [epsilonFactor]
    exact div_ne_zero (mul_ne_zero hγne hθne) hPne
  obtain ⟨r, i, a, hr, hεeq⟩ := exists_eq_C_mul_X_pow_of_mem
    (hε1 ▸ dualSubst_mem_laurentSubalgebra hL₁) (hε2 ▸ hL₂) hεne
  have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  refine ⟨r, hr, (i : ℤ) - a, ?_, fun s hPs hP's => ?_⟩
  · rw [hεeq, map_mul, RatFunc.algebraMap_C, map_pow, map_pow, RatFunc.algebraMap_X,
      zpow_sub₀ hX, zpow_natCast, zpow_natCast, mul_div_assoc]
  · have hx : qs F s ≠ 0 := qs_ne_zero s
    have hθ : dualSubst F (algebraMap ℂ[X] (RatFunc ℂ) (LPolynomial (contragredient π))) =
        algebraMap ℂ[X] (RatFunc ℂ) (dualPoly F (LPolynomial (contragredient π))) /
          algebraMap ℂ[X] (RatFunc ℂ) (X ^ (LPolynomial (contragredient π)).natDegree) := by
      rw [dualSubst_algebraMap, aeval_dualVar]
    have hQ'ne : algebraMap ℂ[X] (RatFunc ℂ) (dualPoly F (LPolynomial (contragredient π))) ≠ 0 := by
      intro h
      apply hθne
      rw [hθ, h, zero_div]
    have hXa : algebraMap ℂ[X] (RatFunc ℂ) (X ^ a) ≠ 0 := by
      rw [map_pow, RatFunc.algebraMap_X]
      exact pow_ne_zero _ hX
    have hXd : algebraMap ℂ[X] (RatFunc ℂ) (X ^ (LPolynomial (contragredient π)).natDegree) ≠ 0 := by
      rw [map_pow, RatFunc.algebraMap_X]
      exact pow_ne_zero _ hX
    have hγeq : gammaFactor F π ψ = algebraMap ℂ[X] (RatFunc ℂ)
        (C r * X ^ i * LPolynomial π * X ^ (LPolynomial (contragredient π)).natDegree) /
        algebraMap ℂ[X] (RatFunc ℂ) (X ^ a * dualPoly F (LPolynomial (contragredient π))) := by
      have h1 : gammaFactor F π ψ = epsilonFactor F π ψ * algebraMap ℂ[X] (RatFunc ℂ) (LPolynomial π) /
          dualSubst F (algebraMap ℂ[X] (RatFunc ℂ) (LPolynomial (contragredient π))) := by
        rw [epsilonFactor]
        field_simp
      rw [h1, hεeq, hθ]
      simp only [map_mul]
      field_simp
    have hQ'x : (dualPoly F (LPolynomial (contragredient π))).eval (qs F s) =
        qs F s ^ (LPolynomial (contragredient π)).natDegree *
          (LPolynomial (contragredient π)).eval (qs F (1 - s)) := by
      rw [qs_one_sub]
      exact eval_dualPoly _ hx
    have hden : (X ^ a * dualPoly F (LPolynomial (contragredient π))).eval (qs F s) ≠ 0 := by
      rw [eval_mul, eval_pow, eval_X, hQ'x]
      exact mul_ne_zero (pow_ne_zero _ hx) (mul_ne_zero (pow_ne_zero _ hx) hP's)
    rw [hγeq, eval_div_algebraMap _ _ hden]
    simp only [LFunction, eval_mul, eval_pow, eval_X, eval_C, hQ'x]
    rw [zpow_sub₀ hx, zpow_natCast, zpow_natCast]
    field_simp

end GodementJacquet

end GroundTheory.Automorphic
