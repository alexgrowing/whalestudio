import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory

theorem algebraMap_mem_maximalRealSubfield_iff {K L : Type} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (x : K) :
    algebraMap K L x ∈ maximalRealSubfield L ↔ x ∈ maximalRealSubfield K := by
  simp only [mem_maximalRealSubfield_iff]
  constructor
  · intro hL ψ
    let : Algebra K ℂ := ψ.toAlgebra
    let φ : L →ₐ[K] ℂ := IsAlgClosed.lift
    have hφ : φ (algebraMap K L x) = ψ x := φ.commutes x
    rw [← hφ]
    exact hL φ.toRingHom
  · intro hK φ
    exact hK (φ.comp (algebraMap K L))

theorem isCMField_of_sq_eq_totallyPositive :
    ∀ (K L : Type) [Field K] [NumberField K] [IsCMField K] [Field L] [NumberField L] [Algebra K L], Module.finrank K L = 2 → ∀ (d : maximalRealSubfield K) (t : L), t ^ 2 = algebraMap K L d → t ∉ Set.range (algebraMap K L) → (∀ φ : maximalRealSubfield K →+* ℝ, 0 < φ d) → IsCMField L ∧ t ∈ maximalRealSubfield L ∧ ∀ x : K, algebraMap K L x ∈ maximalRealSubfield L ↔ x ∈ maximalRealSubfield K := by
  intro K L _ _ _ _ _ _ hKL d t ht2 htK hpos
  have : Module.Finite K L := Module.finite_of_finrank_pos (by omega)
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L

  have htR : t ∈ maximalRealSubfield L := by
    rw [mem_maximalRealSubfield_iff]
    intro φ
    let ρ : maximalRealSubfield K →+* ℂ :=
      (φ.comp (algebraMap K L)).comp (maximalRealSubfield K).subtype
    have hρ : ComplexEmbedding.IsReal ρ := IsTotallyReal.complexEmbedding_isReal ρ
    have hr : (0 : ℝ) < hρ.embedding d := hpos _
    have hsq : φ t * φ t = ((hρ.embedding d : ℝ) : ℂ) := by
      rw [ComplexEmbedding.IsReal.coe_embedding_apply, ← map_mul, ← pow_two, ht2]
      rfl
    have him : (φ t).im = 0 := by
      have h1 := congrArg Complex.re hsq
      have h2 := congrArg Complex.im hsq
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h1 h2
      by_contra hne
      have hre : (φ t).re = 0 := by
        have h3 : (φ t).re * (φ t).im = 0 := by linarith
        rcases mul_eq_zero.mp h3 with h | h
        · exact h
        · exact absurd h hne
      rw [hre] at h1
      nlinarith [sq_nonneg (φ t).im]
    exact Complex.conj_eq_iff_im.mpr him

  have : IsScalarTower (maximalRealSubfield K) K L := inferInstance
  have hKp : Module.finrank (maximalRealSubfield K) K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h4 : Module.finrank (maximalRealSubfield K) L = 4 := by
    rw [← Module.finrank_mul_finrank (maximalRealSubfield K) K L, hKp, hKL]
  have : Module.Finite (maximalRealSubfield K) L := Module.finite_of_finrank_pos (by omega)
  have hint : IsIntegral (maximalRealSubfield K) t := IsIntegral.of_finite _ t

  have hmin : (minpoly (maximalRealSubfield K) t).natDegree = 2 := by
    have hle : (minpoly (maximalRealSubfield K) t).degree ≤ ((2 : ℕ) : WithBot ℕ) := by
      have h := minpoly.degree_le_of_ne_zero (maximalRealSubfield K) t
        (Polynomial.X_pow_sub_C_ne_zero (n := 2) (by norm_num) d)
        (by rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, ht2]; exact sub_self _)
      rwa [Polynomial.degree_X_pow_sub_C (by norm_num)] at h
    have hne1 : (minpoly (maximalRealSubfield K) t).natDegree ≠ 1 := by
      rw [Ne, minpoly.natDegree_eq_one_iff]
      rintro ⟨y, hy⟩
      exact htK ⟨(y : K), hy⟩
    have hpos' := minpoly.natDegree_pos hint
    have h2 := Polynomial.natDegree_le_of_degree_le hle
    omega
  have hbase : ∀ y : maximalRealSubfield K,
      algebraMap (maximalRealSubfield K) L y ∈ maximalRealSubfield L :=
    fun y => (algebraMap_mem_maximalRealSubfield_iff (L := L) (y : K)).mpr y.2

  have hFdeg : Module.finrank (maximalRealSubfield K)
      (IntermediateField.adjoin (maximalRealSubfield K) ({t} : Set L)) = 2 := by
    rw [IntermediateField.adjoin.finrank hint, hmin]
  have hFle' : IntermediateField.adjoin (maximalRealSubfield K) ({t} : Set L) ≤
      (maximalRealSubfield L).toIntermediateField hbase :=
    IntermediateField.adjoin_simple_le_iff.mpr htR
  have hFle : ∀ y ∈ IntermediateField.adjoin (maximalRealSubfield K) ({t} : Set L),
      y ∈ maximalRealSubfield L := fun y hy => hFle' hy
  generalize IntermediateField.adjoin (maximalRealSubfield K) ({t} : Set L) = F at hFdeg hFle
  have hFL : Module.finrank F L = 2 := by
    have h := Module.finrank_mul_finrank (maximalRealSubfield K) F L
    rw [hFdeg, h4] at h
    omega
  have : Module.Finite F L := Module.finite_of_finrank_pos (by omega)
  let ι : F →+* maximalRealSubfield L :=
    { toFun := fun y => ⟨y.1, hFle y.1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let : Algebra F (maximalRealSubfield L) := ι.toAlgebra
  have : IsScalarTower F (maximalRealSubfield L) L := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.of_finite F L
  have : Algebra.IsAlgebraic F (maximalRealSubfield L) :=
    Algebra.IsAlgebraic.tower_bot F (maximalRealSubfield L) L
  have : IsTotallyReal F := IsTotallyReal.of_algebra F (maximalRealSubfield L)
  have : Algebra.IsQuadraticExtension F L := ⟨hFL⟩
  have : IsTotallyComplex L := ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mp fun h =>
    InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _)
      (InfinitePlace.IsReal.comap (algebraMap K L) h)⟩
  exact ⟨IsCMField.ofCMExtension F L, htR, fun x => algebraMap_mem_maximalRealSubfield_iff x⟩

end GlobalTheory
