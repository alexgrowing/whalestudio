import Formalism.SharpRestriction.GrowthBounds.RootWeights.PolynomialOperatorsGlRelations

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem v2con_X_pderiv {R : Type*} [CommRing R] {σ : Type*} (v w : σ) (m : σ →₀ ℕ) (c : R) :
    (X v : MvPolynomial σ R) * pderiv w (monomial m c) =
      monomial (m - Finsupp.single w 1 + Finsupp.single v 1) (c * (m w : R)) := by
  rw [pderiv_monomial, show (X v : MvPolynomial σ R) = monomial (Finsupp.single v 1) 1 from rfl,
    monomial_mul, one_mul, add_comm (Finsupp.single v 1)]

theorem v2con_X_pderiv_self {R : Type*} [CommRing R] {σ : Type*} (v : σ) (m : σ →₀ ℕ) (c : R) :
    (X v : MvPolynomial σ R) * pderiv v (monomial m c) = monomial m (c * (m v : R)) := by
  rw [v2con_X_pderiv]
  by_cases h : m v = 0
  · simp [h]
  · have hle : Finsupp.single v 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    rw [tsub_add_cancel_of_le hle]

theorem v2con_diag {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (m : ι × Fin n →₀ ℕ) (c : R) :
    glAct R LL S a a (monomial m c) = monomial m (((wtS LL S m a : ℤ) : R) * c) := by
  classical
  unfold glAct wtS
  rw [LinearMap.sum_apply]
  simp only [Int.cast_sum, Finset.sum_mul]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  by_cases h1 : l ∈ S <;> by_cases h2 : LL.vec l = true <;>
    simp [h1, h2, -pderiv_monomial, v2con_X_pderiv_self, mul_comm]

theorem v2con_coeff_diag {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (x : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    coeff m (glAct R LL S a a x) = ((wtS LL S m a : ℤ) : R) * coeff m x := by
  classical
  induction x using MvPolynomial.induction_on' with
  | monomial m' c =>
    rw [v2con_diag, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · simp
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

theorem monomials_are_weight_vectors : MonomialsAreWeightVectors := by
  intro R _ _ ι _ LL n S
  constructor
  · intro m c
    rw [weightSp, Submodule.mem_iInf]
    intro a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    change glAct R LL S a a (monomial m c) - _ = 0
    rw [v2con_diag, smul_monomial, smul_eq_mul, sub_self]
  · intro ν x hx m hm
    rw [weightSp, Submodule.mem_iInf] at hx
    funext a
    have h := hx a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at h
    have h2 := congrArg (coeff m) h
    change coeff m (glAct R LL S a a x) = _ at h2
    rw [v2con_coeff_diag, coeff_smul, smul_eq_mul] at h2
    have hc : coeff m x ≠ 0 := mem_support_iff.mp hm
    have h3 := mul_right_cancel₀ hc h2
    exact_mod_cast h3

theorem v2con_stable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (N : ℕ) (a b : Fin n) (x : MvPolynomial (ι × Fin n) R)
    (hx : x ∈ restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N}) :
    glAct R LL S a b x ∈ restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N} := by
  classical
  rw [mem_restrictSupport_iff] at hx
  have hmono : ∀ (m' : ι × Fin n →₀ ℕ) (c' : R), m'.degree ≤ N →
      monomial m' c' ∈ restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N} := by
    intro m' c' hm'
    rw [mem_restrictSupport_iff]
    intro y hy
    have := Finset.mem_singleton.mp (support_monomial_subset hy)
    subst this
    exact hm'
  have hterm : ∀ (m : ι × Fin n →₀ ℕ) (c : R) (u w : ι × Fin n), m.degree ≤ N →
      (X u : MvPolynomial (ι × Fin n) R) * pderiv w (monomial m c) ∈
        restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N} := by
    intro m c u w hm
    rw [v2con_X_pderiv]
    by_cases h0 : m w = 0
    · simp [h0]
    · apply hmono
      have hle : Finsupp.single w 1 ≤ m := by
        rw [Finsupp.single_le_iff]; omega
      have e1 : (m - Finsupp.single w 1).degree + 1 = m.degree := by
        have := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
        rw [map_add, Finsupp.degree_single] at this
        exact this
      rw [map_add, Finsupp.degree_single]
      omega
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  have hdeg : m.degree ≤ N := hx hm
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ (fun l _ => ?_)
  split_ifs
  · exact hterm m _ _ _ hdeg
  · rw [LinearMap.neg_apply]
    exact Submodule.neg_mem _ (hterm m _ _ _ hdeg)
  · exact Submodule.zero_mem _

theorem polynomial_locally_finite : PolynomialLocallyFinite := by
  intro R _ ι _ LL n S x
  classical
  refine ⟨restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ x.totalDegree}, ?_, ?_, ?_⟩
  · haveI : Finite {m : ι × Fin n →₀ ℕ | m.degree ≤ x.totalDegree} :=
      (Finsupp.finite_of_degree_le x.totalDegree).to_subtype
    exact Module.Finite.of_basis (basisRestrictSupport R _)
  · rw [mem_restrictSupport_iff]
    intro m hm
    show m.degree ≤ x.totalDegree
    rw [Finsupp.degree_apply]
    exact le_totalDegree hm
  · intro a b y hy
    exact v2con_stable LL S _ a b y hy

end Formalism.MainNotions.G.GLWeightTheory
