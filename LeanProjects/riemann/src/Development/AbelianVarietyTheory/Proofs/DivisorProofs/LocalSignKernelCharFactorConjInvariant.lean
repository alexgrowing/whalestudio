import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.BCT.ConjugationGramUnitary

open Formalism.UG

theorem negOne_zpow_ordL_mul {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (a x : L) (ha : a ≠ 0) :
    (-1 : ℂ) ^ ordL (σ a * a * x) = (-1 : ℂ) ^ ordL x := by
  have key : ∀ (y : L) (m : ℤ), Valued.v y = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
      ordL y = m := by
    intro y m h
    have hne : Valued.v y ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
    unfold ordL
    rw [dif_neg hne]
    have e : ((WithZero.unzero hne : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = Multiplicative.ofAdd (-m) := by
      rw [WithZero.coe_unzero, h]
    rw [WithZero.coe_inj.mp e]
    simp
  have spec : ∀ y : L, y ≠ 0 → Valued.v y = ((Multiplicative.ofAdd (-(ordL y)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro y hy
    have hne : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    unfold ordL
    rw [dif_neg hne]
    simp
  by_cases hx : x = 0
  · simp [hx]
  have h1 : ordL (σ a * a * x) = 2 * ordL a + ordL x := by
    apply key
    rw [map_mul, map_mul, hσ, spec a ha, spec x hx]
    rw [← WithZero.coe_mul, ← WithZero.coe_mul]
    congr 1
    rw [← ofAdd_add, ← ofAdd_add]
    congr 1
    ring
  rw [h1, zpow_add₀ (by norm_num), Even.neg_one_zpow (even_two_mul _), one_mul]

def gram {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {ι : Type} (v : ι → (Fin n → K)) : Matrix ι ι K :=
  Matrix.of fun i j => ∑ k, σ (v i k) * v j k

theorem gram_basis {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (V : Submodule K (Fin n → K)) {ι : Type} [Fintype ι]
    [DecidableEq ι] (b c : Module.Basis ι K V) :
    gram σ (fun i => (c i : Fin n → K)) =
      ((b.toMatrix c).map σ)ᵀ * gram σ (fun i => (b i : Fin n → K)) * b.toMatrix c := by
  have hc : ∀ j k, (c j : Fin n → K) k = ∑ l, b.toMatrix c l j * (b l : Fin n → K) k := by
    intro j k
    have := b.sum_toMatrix_smul_self c j
    rw [← this, Submodule.coe_sum, Finset.sum_apply]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  ext i j
  simp only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hc, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem gram_unitary {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : (g.map σ)ᵀ * g = 1) {ι : Type} (v : ι → (Fin n → K)) :
    gram σ (fun i => g *ᵥ v i) = gram σ v := by
  have he : ∀ a b, ∑ k, σ (g k a) * g k b = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun hg a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hm : ∀ (x : Fin n → K) k, (g *ᵥ x) k = ∑ a, g k a * x a := fun _ _ => rfl
  ext i j
  simp only [gram, Matrix.of_apply, hm, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  have : ∀ y, ∑ k, σ (g k y) * σ (v i y) * (g k a * v j a) = σ (v i y) * v j a * (if y = a then 1 else 0) := by
    intro y
    rw [← he y a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem aeval_conj {K : Type} [Field K] {n : ℕ} (γ g : GL (Fin n) K) (Q : K[X]) :
    aeval (g⁻¹ * γ * g).val Q = (g⁻¹).val * aeval γ.val Q * g.val := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, Matrix.mul_add, Matrix.add_mul]
  | monomial k a =>
    simp only [aeval_monomial, Units.val_mul]
    have : ((g⁻¹).val * γ.val * g.val) ^ k = (g⁻¹).val * γ.val ^ k * g.val := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        simp only [Matrix.mul_assoc]
        congr 2
        rw [← Matrix.mul_assoc g.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [this]
    simp [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.BCT.ConjugationGramUnitary

namespace GlobalTheory.BCT

open GlobalTheory.BCT.ConjugationGramUnitary

theorem kapSign_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ (Q₁ : (w.adicCompletion E)[X]) (γ g : UL n w), kapSign n w Q₁ (g⁻¹ * γ * g).1 = kapSign n w Q₁ γ.1 := by
  intro E _ _ _ n w hv Q₁ γ g
  unfold kapSign
  split_ifs with hs
  · rfl
  have hg : ((g.1.val).map (cj w))ᵀ * g.1.val = 1 := by
    have h := g.2
    simp only [UL, hs, if_false] at h
    have h2 : Formalism.UG.cT (cj w) (g.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 * (g.1 : Matrix (Fin n) (Fin n) _) = 1 := h
    simpa [Formalism.UG.cT] using h2
  have hinv : ((g.1)⁻¹).val * g.1.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinv' : g.1.val * ((g.1)⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hM : aeval ((g⁻¹ * γ * g).1).val Q₁ = ((g.1)⁻¹).val * aeval γ.1.val Q₁ * g.1.val := by
    have : (g⁻¹ * γ * g).1 = g.1⁻¹ * γ.1 * g.1 := by simp
    rw [this]
    exact aeval_conj _ _ _
  dsimp only
  let V := LinearMap.ker (Matrix.toLin' (aeval γ.1.val Q₁))
  let V' := LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : UL n w) : GLw n w).val Q₁))
  have hmem : ∀ x, x ∈ V' ↔ g.1.val *ᵥ x ∈ V := by
    intro x
    simp only [V, V', LinearMap.mem_ker, Matrix.toLin'_apply]
    rw [hM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    constructor
    · intro h
      have := congrArg (g.1.val *ᵥ ·) h
      simpa [Matrix.mulVec_mulVec, hinv'] using this
    · intro h
      rw [h, Matrix.mulVec_zero]
  have hinj : Function.Injective (Matrix.toLin' g.1.val) := by
    intro x y h
    have := congrArg (((g.1)⁻¹).val *ᵥ ·) h
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hinv] using this
  have hmap : V'.map (Matrix.toLin' g.1.val) = V := by
    ext x
    simp only [Submodule.mem_map, Matrix.toLin'_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem y).mp hy
    · intro hx
      refine ⟨((g.1)⁻¹).val *ᵥ x, ?_, ?_⟩
      · rw [hmem, Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
        exact hx
      · rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
  let e : V' ≃ₗ[w.adicCompletion E] V :=
    (Submodule.equivMapOfInjective _ hinj V').trans (LinearEquiv.ofEq _ _ hmap)
  let b := Module.finBasis (w.adicCompletion E) V
  let b' := Module.finBasis (w.adicCompletion E) V'
  let c₀ := b'.map e
  let c := c₀.reindex (b.indexEquiv c₀).symm
  have hc₀ : ∀ i, (c₀ i : Fin n → w.adicCompletion E) = g.1.val *ᵥ (b' i : Fin n → w.adicCompletion E) := by
    intro i
    rfl
  have h1 : gram (cj w) (fun i => (b' i : Fin n → w.adicCompletion E)) =
      gram (cj w) (fun i => (c₀ i : Fin n → w.adicCompletion E)) := by
    simp only [hc₀]
    exact (gram_unitary (cj w) _ hg _).symm
  have h2 : (gram (cj w) (fun i => (c₀ i : Fin n → w.adicCompletion E))).det =
      (gram (cj w) (fun i => (c i : Fin n → w.adicCompletion E))).det := by
    have : gram (cj w) (fun i => (c i : Fin n → w.adicCompletion E)) =
        (gram (cj w) (fun i => (c₀ i : Fin n → w.adicCompletion E))).submatrix (b.indexEquiv c₀) (b.indexEquiv c₀) := by
      ext i j
      simp [ConjugationGramUnitary.gram, c, Module.Basis.reindex_apply]
    rw [this, Matrix.det_submatrix_equiv_self]
  let A := b.toMatrix c
  have hA : A.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse (b.toMatrix_mul_toMatrix_flip c)
  have h3 : (gram (cj w) (fun i => (c i : Fin n → w.adicCompletion E))).det =
      cj w A.det * A.det * (gram (cj w) (fun i => (b i : Fin n → w.adicCompletion E))).det := by
    have hd : ((b.toMatrix c).map (cj w)).det = cj w A.det := by rw [RingHom.map_det]; rfl
    rw [gram_basis (cj w) V b c, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hd]
    ring
  change (-1 : ℂ) ^ Formalism.UG.ordL (gram (cj w) (fun i => (b' i : Fin n → w.adicCompletion E))).det =
    (-1 : ℂ) ^ Formalism.UG.ordL (gram (cj w) (fun i => (b i : Fin n → w.adicCompletion E))).det
  rw [h1, h2, h3]
  exact negOne_zpow_ordL_mul (cj w) hv _ _ hA

end GlobalTheory.BCT
