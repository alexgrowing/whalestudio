import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DblTrace

open Matrix

theorem hTens_dbl {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E)
    (x y : Matrix α (β ⊕ β) E) :
    hTens c JA (dbl JB) x y = hTens c JA JB x.toCols₁ y.toCols₁ + hTens c JA (-JB) x.toCols₂ y.toCols₂ := by
  simp only [hTens, dbl, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, toCols₁, toCols₂,
    of_apply, ← Finset.sum_add_distrib]

theorem rhs_dbl {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n] (A : Matrix m m K)
    (X U : Matrix m (n ⊕ n) K) (B : Matrix n n K) :
    ∑ k, ∑ l, (-(A * X * (fromBlocks B 0 0 (-B))ᵀ)) k l * U k l =
      ∑ k, ∑ l, (-(A * X.toCols₁ * Bᵀ)) k l * U.toCols₁ k l +
        ∑ k, ∑ l, (-(A * X.toCols₂ * (-B)ᵀ)) k l * U.toCols₂ k l := by
  have hX : A * X = fromCols (A * X.toCols₁) (A * X.toCols₂) := by
    conv_lhs => rw [← fromCols_toCols X]
    rw [mul_fromCols]
  rw [hX, fromBlocks_transpose, fromCols_mul_fromBlocks]
  simp [Fintype.sum_sum_type, Finset.sum_add_distrib, toCols₁, toCols₂]
  ring

end GlobalTheory.DblTrace

open GlobalTheory.DblTrace in
theorem GlobalTheory.DblTrace.trace_pairing_dbl : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    IsCMExt F E σ → ∀ {v : Pl F} (τ : E →ₐ[F] Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E)
    (JB : Matrix (Fin n) (Fin n) E), (∀ i j, σ (JA j i) = JA i j) → (∀ i j, σ (JB j i) = -JB i j) →
    ∀ (x u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)), x.map (piW τ) = 0 → u.map (piW (τ.comp σ)) = 0 →
    piW τ (hTens (cA σ) (incM F JA) (dbl (incM F JB)) x u) + piW (τ.comp σ) (hTens (cA σ) (incM F JA) (dbl (incM F JB)) x u) =
      ∑ k, ∑ l, (-(JA.map τ * x.map (piW (τ.comp σ)) * ((dbl JB).map τ)ᵀ)) k l * u.map (piW τ) k l := by
  intro F E _ _ _ _ _ σ hcm v τ m n JA JB hA hB x u hx hu
  have hneg : incM F (-JB) = -incM F JB := by
    simp [incM, Matrix.map_neg]
  have hB' : ∀ i j, σ ((-JB) j i) = -(-JB) i j := by
    intro i j; simp [hB]
  have h1 : x.toCols₁.map (piW τ) = 0 := by
    exact Matrix.ext fun i j => congrFun (congrFun hx i) (Sum.inl j)
  have h2 : u.toCols₁.map (piW (τ.comp σ)) = 0 := by
    exact Matrix.ext fun i j => congrFun (congrFun hu i) (Sum.inl j)
  have h3 : x.toCols₂.map (piW τ) = 0 := by
    exact Matrix.ext fun i j => congrFun (congrFun hx i) (Sum.inr j)
  have h4 : u.toCols₂.map (piW (τ.comp σ)) = 0 := by
    exact Matrix.ext fun i j => congrFun (congrFun hu i) (Sum.inr j)
  have hd : (dbl JB).map τ = Matrix.fromBlocks (JB.map τ) 0 0 (-(JB.map τ)) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [dbl]
  rw [hTens_dbl, ← hneg, map_add, map_add, add_add_add_comm, GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm τ JA JB hA hB _ _ h1 h2,
    GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm τ JA (-JB) hA hB' _ _ h3 h4, hd, rhs_dbl]
  have hm : (-JB).map τ = -(JB.map τ) := by ext i j; simp
  rw [hm]
  rfl
