import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsHomogeneousOfEquivariant
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality

set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
namespace GlobalTheory.ChowHt.Model

theorem isChowForm_point (k : Type) [Field k] :
    IsChowForm (Ideal.span {(X 1 : MvPolynomial (Fin 2) k)}) 0 1 (X (0, 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs b
    rw [support_X, Finset.mem_singleton] at hs
    subst hs
    fin_cases b
    simp [Fin.sum_univ_two, Finsupp.single_apply]
  · rw [map_X]; exact X_prime.irreducible
  · intro u
    rw [aeval_X]
    constructor
    · intro h
      refine ⟨![1, 0], by simp, ?_, ?_⟩
      · intro g hg
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hg
        simp
      · intro i
        fin_cases i
        simpa [Fin.sum_univ_two] using h
    · rintro ⟨y, hy, hI, hu⟩
      have h1 : y 1 = 0 := by simpa using hI (X 1) (Ideal.subset_span rfl)
      have h0 : y 0 ≠ 0 := by
        intro h0; apply hy; funext j; fin_cases j <;> simp [h0, h1]
      have := hu 0
      simp [Fin.sum_univ_two, h1, h0] at this
      exact this

def linForm {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) : MvPolynomial (Fin 1 × Fin N) R :=
  ∑ j, C (c j) * X (0, j)

theorem linSubst_linForm {R : Type} [CommRing R] {N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (c : Fin N → R) : linSubst M (linForm c) = linForm (fun k => ∑ j, M j k * c j) := by
  simp only [linSubst, linForm, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

set_option autoImplicit false in
open MvPolynomial NumberField in
theorem _root_.GlobalTheory.ChowHt.Model.coeff_linForm {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R)
    (k : Fin N) :
    (_root_.GlobalTheory.ChowHt.Model.linForm c).coeff (Finsupp.single (0, k) 1) = c k := by
  classical
  simp only [_root_.GlobalTheory.ChowHt.Model.linForm, coeff_sum, coeff_C_mul, coeff_X']
  have key : ∀ j : Fin N,
      (Finsupp.single ((0 : Fin 1), j) 1 = Finsupp.single ((0 : Fin 1), k) 1) ↔ j = k := by
    intro j
    constructor
    · intro h
      have := Finsupp.single_left_injective (one_ne_zero) h
      simpa using this
    · rintro rfl; rfl
  simp [key]

theorem gaussAbs_linForm {F : Type} [Field F] [NumberField F] {N : ℕ} (v : FinitePlace F)
    (c : Fin N → F) : ReciprocityTheory.MultiplicativeHeights.gaussAbs v (linForm c) = ⨆ k, v (c k) := by
  classical
  have hb : BddAbove (Set.range fun k => v (c k)) := (Set.finite_range _).bddAbove
  have hn : 0 ≤ ⨆ k, v (c k) := Real.iSup_nonneg fun k => apply_nonneg _ _
  unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs
  apply le_antisymm
  · rw [← Real.coe_toNNReal _ hn, NNReal.coe_le_coe]
    refine Finset.sup_le fun s hs => Real.toNNReal_le_toNNReal ?_
    by_cases h : ∃ k, s = Finsupp.single (0, k) 1
    · obtain ⟨k, rfl⟩ := h
      rw [coeff_linForm]; exact le_ciSup hb k
    · exfalso
      rw [mem_support_iff] at hs
      apply hs
      simp only [linForm, coeff_sum, coeff_C_mul, coeff_X']
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg, mul_zero]
      intro h'; exact h ⟨j, h'.symm⟩
  · refine Real.iSup_le (fun k => ?_) (NNReal.coe_nonneg _)
    by_cases h : c k = 0
    · simp [h]
    · have hm : Finsupp.single ((0 : Fin 1), k) 1 ∈ (linForm c).support := by
        rw [mem_support_iff, coeff_linForm]; exact h
      have := Finset.le_sup (f := fun s => (v ((linForm c).coeff s)).toNNReal) hm
      simp only [coeff_linForm] at this
      have h2 := NNReal.coe_le_coe.2 this
      rwa [Real.coe_toNNReal _ (apply_nonneg _ _)] at h2

theorem blockSphereMean_linForm {N : ℕ} (c : Fin N → ℂ) (hc : c ≠ 0) :
    ReciprocityTheory.MultiplicativeHeights.blockSphereMean 1 N (linForm c) =
      Real.log (Real.sqrt (∑ i, ‖c i‖ ^ 2)) - (harmonic (N - 1) : ℝ) / 2 := by
  have h := (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLinLog N (WithLp.toLp 2 c) (by simpa using hc)).2
  rw [EuclideanSpace.norm_eq] at h
  simp only at h
  rw [← h]
  unfold ReciprocityTheory.MultiplicativeHeights.blockSphereMean ReciprocityTheory.MultiplicativeHeights.blockSphereProb
  rw [← (MeasureTheory.measurePreserving_funUnique (ReciprocityTheory.MultiplicativeHeights.sphereProb N) (Fin 1)).integral_comp']
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp [linForm, ReciprocityTheory.MultiplicativeHeights.blockPoint]

theorem formHeight_linForm {F : Type} [Field F] [NumberField F] {N n : ℕ}
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ σ, (A σ).det ≠ 0) (y : Fin N → F) (hy : y ≠ 0) :
    formHeight 1 w A (linForm y) = pointHeight w A y := by
  unfold formHeight pointHeight
  congr 2
  · simp [linSubst_linForm, gaussAbs_linForm]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    have hm : MvPolynomial.map σ (linForm y) = linForm (fun j => σ (y j)) := by
      simp [linForm]
    have hσ : σ.comp (algebraMap F F) = σ := by ext; simp
    rw [hm, linSubst_linForm, blockSphereMean_linForm, hσ]
    · simp
    · intro h
      apply hy
      have : Matrix.vecMul (fun j => σ (y j)) (A σ) = 0 := by
        funext k
        have := congrFun h k
        simpa [Matrix.vecMul, dotProduct, mul_comm] using this
      have h2 := Matrix.eq_zero_of_vecMul_eq_zero (hA σ) this
      funext j
      simpa using congrFun h2 j

theorem isChowForm_line (k : Type) [Field k] :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) k)) 1 1
      (Matrix.of fun i j : Fin 2 => (X (i, j) : MvPolynomial (Fin 2 × Fin 2) k)).det := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro s hs b
    rw [Matrix.det_fin_two] at hs
    simp only [Matrix.of_apply, X, monomial_mul, mul_one] at hs
    have h1 := support_sub _ _ _ hs
    rw [Finset.mem_union] at h1
    rcases h1 with h | h <;>
    · have := support_monomial_subset h
      rw [Finset.mem_singleton] at this
      subst this
      fin_cases b <;> simp [Fin.sum_univ_two, Finsupp.single_apply]
  · have := GlobalTheory.BorelAlg.irreducible_det' (R := AlgebraicClosure k) (k := 2) (by norm_num) id
      Function.injective_id
    convert this using 1
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp
  · intro u
    have : MvPolynomial.aeval u
        (Matrix.of fun i j : Fin 2 => (X (i, j) : MvPolynomial (Fin 2 × Fin 2) k)).det =
        (Matrix.of fun i j : Fin 2 => u (i, j)).det := by
      simp [Matrix.det_fin_two]
    rw [this, ← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨y, hy, h⟩
      refine ⟨y, hy, fun g hg => by simp [Ideal.mem_bot.1 hg], fun i => ?_⟩
      simpa [Matrix.mulVec, dotProduct] using congrFun h i
    · rintro ⟨y, hy, -, h⟩
      refine ⟨y, hy, funext fun i => ?_⟩
      simpa [Matrix.mulVec, dotProduct] using h i

theorem not_isChowForm_top {k : Type} [Field k] {N D δ : ℕ}
    (f : MvPolynomial (Fin (D + 1) × Fin N) k) : ¬ IsChowForm (⊤ : Ideal (MvPolynomial (Fin N) k)) D δ f := by
  intro h
  have hz : ∀ u : Fin (D + 1) × Fin N → AlgebraicClosure k, MvPolynomial.aeval u f ≠ 0 := by
    intro u hu
    obtain ⟨y, -, hI, -⟩ := (h.zero_iff u).1 hu
    simpa using hI 1 trivial
  apply h.irred.not_isUnit
  rw [← Ideal.span_singleton_eq_top]
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨x, rfl⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton).1 hM
  have := hle (Ideal.subset_span rfl)
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at this
  apply hz x
  simpa [MvPolynomial.aeval_map_algebraMap] using this

end GlobalTheory.ChowHt.Model
