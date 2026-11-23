import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Algebra Cardinal

noncomputable section

universe u w

namespace DimTie

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

abbrev ratioRing (y : Fin (N + 1) → Ω) : Subalgebra k Ω :=
  Algebra.adjoin k {a | ∃ i j, y i ≠ 0 ∧ a = y j / y i}

theorem ratio_mem (y : Fin (N + 1) → Ω) {i : Fin (N + 1)} (hi : y i ≠ 0) (j : Fin (N + 1)) :
    y j / y i ∈ ratioRing (k := k) y :=
  Algebra.subset_adjoin ⟨i, j, hi, rfl⟩

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem trdeg_funField (y : Fin (N + 1) → Ω) :
    trdeg k (funField (k := k) y) = trdeg k (ratioRing (k := k) y) := by
  have : FaithfulSMul k (ratioRing (k := k) y) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k _).injective
  show trdeg k (IntermediateField.adjoin k {a | ∃ i j, y i ≠ 0 ∧ a = y j / y i}) = _
  rw [← trdeg_add_eq k (ratioRing (k := k) y)
    (A := IntermediateField.adjoin k {a | ∃ i j, y i ≠ 0 ∧ a = y j / y i}),
    trdeg_eq_zero (R := ratioRing (k := k) y)
      (A := IntermediateField.adjoin k {a | ∃ i j, y i ≠ 0 ∧ a = y j / y i}), add_zero]

theorem trdeg_polynomial (D : Type w) [CommRing D] [IsDomain D] [Algebra k D] [FaithfulSMul k D] :
    trdeg k (Polynomial D) = trdeg k D + 1 := by
  have : FaithfulSMul D (Polynomial D) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Polynomial.C_injective
  rw [← trdeg_add_eq k D (A := Polynomial D), Polynomial.trdeg_of_isDomain]

theorem aeval_C_mul_X_injective {c : Ω} (hc : c ≠ 0) :
    Function.Injective (Polynomial.aeval (R := Ω) (Polynomial.C c * Polynomial.X)) := by
  have h : (Polynomial.aeval (R := Ω) (Polynomial.C c⁻¹ * Polynomial.X)).comp
      (Polynomial.aeval (Polynomial.C c * Polynomial.X)) = AlgHom.id Ω (Polynomial Ω) := by
    refine Polynomial.algHom_ext ?_
    simp only [AlgHom.comp_apply, Polynomial.aeval_X, map_mul, Polynomial.aeval_C,
      Polynomial.algebraMap_eq, AlgHom.id_apply]
    rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1, one_mul]
  exact Function.LeftInverse.injective (g := Polynomial.aeval (Polynomial.C c⁻¹ * Polynomial.X))
    fun p => by rw [← AlgHom.comp_apply, h, AlgHom.id_apply]

section Cone

variable (y : Fin (N + 1) → Ω) {i₀ : Fin (N + 1)} (hi₀ : y i₀ ≠ 0)

def ratio (j : Fin (N + 1)) : ratioRing (k := k) y := ⟨y j / y i₀, ratio_mem y hi₀ j⟩

def dehom : Poly k N →ₐ[k] Polynomial (ratioRing (k := k) y) :=
  aeval fun j => Polynomial.C (ratio y hi₀ j) * Polynomial.X

variable (i₀) in

def rehom : Polynomial (ratioRing (k := k) y) →ₐ[k] Polynomial Ω :=
  ((Polynomial.aeval (R := Ω) (Polynomial.C (y i₀) * Polynomial.X)).restrictScalars k).comp
    (Polynomial.mapAlgHom (ratioRing (k := k) y).val)

include hi₀ in
theorem rehom_injective : Function.Injective (rehom (k := k) y i₀) := by
  rw [rehom, AlgHom.coe_comp]
  exact (aeval_C_mul_X_injective hi₀).comp (Polynomial.map_injective _ Subtype.val_injective)

theorem rehom_comp_dehom : (rehom (k := k) y i₀).comp (dehom y hi₀) = cone (S := k) y := by
  refine MvPolynomial.algHom_ext fun j => ?_
  have hc : (cone (S := k) y) (X j) = Polynomial.C (y j) * Polynomial.X := by
    simp [cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]
  rw [hc]
  simp [rehom, dehom, ratio]
  rw [← mul_assoc, ← Polynomial.C_mul, div_mul_cancel₀ _ hi₀]

theorem primeOf_eq_ker : primeOf (S := k) y = RingHom.ker (dehom (k := k) y hi₀) := by
  ext f
  rw [primeOf_eq, RingHom.mem_ker, RingHom.mem_ker, ← rehom_comp_dehom (k := k) y hi₀, AlgHom.comp_apply,
    map_eq_zero_iff _ (rehom_injective (k := k) y hi₀)]

theorem isAlgebraic_range :
    Algebra.IsAlgebraic (dehom (k := k) y hi₀).range (Polynomial (ratioRing (k := k) y)) := by
  set R := (dehom (k := k) y hi₀).range
  have hmem : ∀ j, Polynomial.C (ratio (k := k) y hi₀ j) * Polynomial.X ∈ R :=
    fun j => ⟨X j, by simp [dehom]⟩
  have h1 : ratio (k := k) y hi₀ i₀ = 1 := Subtype.ext (div_self hi₀)
  have hX : IsAlgebraic R (Polynomial.X : Polynomial (ratioRing (k := k) y)) := by
    have h := hmem i₀
    rw [h1, Polynomial.C_1, one_mul] at h
    exact isAlgebraic_algebraMap (⟨_, h⟩ : R)
  have hb : ∀ j, IsAlgebraic R (Polynomial.C (ratio (k := k) y hi₀ j)) := fun j =>
    IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero Polynomial.X_ne_zero) hX
      (by rw [mul_comm]; exact isAlgebraic_algebraMap (⟨_, hmem j⟩ : R))
  have hgen : ∀ i j (hi : y i ≠ 0),
      IsAlgebraic R (Polynomial.C (⟨y j / y i, ratio_mem y hi j⟩ : ratioRing (k := k) y)) := by
    intro i j hi
    have hne : ratio (k := k) y hi₀ i ≠ 0 := fun h =>
      div_ne_zero hi hi₀ (congrArg Subtype.val h)
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero (Polynomial.C_ne_zero.mpr hne))
      (hb i) ?_
    have he : ratio (k := k) y hi₀ i * ⟨y j / y i, ratio_mem y hi j⟩ = ratio (k := k) y hi₀ j := by
      apply Subtype.ext
      change y i / y i₀ * (y j / y i) = y j / y i₀
      field_simp
    rw [← Polynomial.C_mul, he]
    exact hb j
  have hCD : ∀ d : ratioRing (k := k) y, IsAlgebraic R (Polynomial.C d) := by
    let M : Subalgebra k (ratioRing (k := k) y) :=
      ((Subalgebra.algebraicClosure R (Polynomial (ratioRing (k := k) y))).restrictScalars k).comap
        (Polynomial.CAlgHom (R := k) (A := ratioRing (k := k) y))
    have hM : ratioRing (k := k) y ≤ M.map (ratioRing (k := k) y).val := Algebra.adjoin_le (by
      rintro _ ⟨i, j, hi, rfl⟩
      exact ⟨⟨y j / y i, ratio_mem y hi j⟩, hgen i j hi, rfl⟩)
    intro d
    obtain ⟨d', hd', he⟩ := hM d.2
    rw [show d = d' from Subtype.ext he.symm]
    exact hd'
  refine ⟨fun p => ?_⟩
  induction p using Polynomial.induction_on with
  | C a => exact hCD a
  | add p q hp hq => exact hp.add hq
  | monomial n a h => rw [pow_succ, ← mul_assoc]; exact h.mul hX

theorem trdeg_range :
    trdeg k (dehom (k := k) y hi₀).range = trdeg k (ratioRing (k := k) y) + 1 := by
  have := isAlgebraic_range (k := k) y hi₀
  have : FaithfulSMul k (dehom (k := k) y hi₀).range :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k _).injective
  have := (faithfulSMul_iff_algebraMap_injective (dehom (k := k) y hi₀).range
    (Polynomial (ratioRing (k := k) y))).2 Subtype.val_injective
  have : FaithfulSMul k (ratioRing (k := k) y) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k _).injective
  rw [← trdeg_polynomial (k := k) (ratioRing (k := k) y), ← trdeg_add_eq k (dehom (k := k) y hi₀).range
    (A := Polynomial (ratioRing (k := k) y)),
    trdeg_eq_zero (R := (dehom (k := k) y hi₀).range) (A := Polynomial (ratioRing (k := k) y)),
    add_zero]

end Cone

theorem ringKrullDim_eq (y : Fin (N + 1) → Ω) (hy : y ≠ 0) :
    ringKrullDim (Poly k N ⧸ primeOf (S := k) y) =
      (((trdeg k (funField (k := k) y)).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hy
  have hi₀ : y i₀ ≠ 0 := hi₀
  have : Algebra.FiniteType k (Poly k N ⧸ primeOf (S := k) y) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _)
      (Ideal.Quotient.mkₐ_surjective k _)
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg k]
  have hk : primeOf (S := k) y = RingHom.ker (dehom (k := k) y hi₀).rangeRestrict := by
    rw [primeOf_eq_ker (k := k) y hi₀]
    ext f
    simp only [RingHom.mem_ker]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  let e : (Poly k N ⧸ primeOf (S := k) y) ≃ₐ[k] (dehom (k := k) y hi₀).range :=
    (Ideal.quotientEquivAlgOfEq k hk).trans
      (Ideal.quotientKerAlgEquivOfSurjective (dehom (k := k) y hi₀).rangeRestrict_surjective)
  have h := AlgEquiv.lift_trdeg_eq (R := k) (A := Poly k N ⧸ primeOf (S := k) y)
    (A' := (dehom (k := k) y hi₀).range) e
  rw [trdeg_range (k := k) y hi₀, ← trdeg_funField] at h
  have h2 := congrArg Cardinal.toENat h
  simp only [toENat_lift, map_add, map_one] at h2
  rw [h2]

end DimTie

theorem DimTie.proof : DimTie.Statement := by
  intro k _ Ω _ _ N y hy e
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hy
  have hi₀ : y i₀ ≠ 0 := hi₀
  have hdim := DimTie.ringKrullDim_eq (k := k) y hy
  constructor
  · intro h
    have h' := h.dim
    rw [hdim] at h'
    have h3 : (trdeg k (funField (k := k) y)).toENat + 1 = (e : ℕ∞) + 1 := by exact_mod_cast h'
    exact Cardinal.toENat_eq_natCast.mp ((ENat.add_left_injective_of_ne_top ENat.one_ne_top) h3)
  · intro h
    have h' : trdeg k (funField (k := k) y) = e := h
    refine ⟨inferInstance, fun p hp d => homogeneousComponent_mem_primeOf y hp d, le_rfl, ⟨i₀, ?_⟩, ?_⟩
    · rw [mem_primeOf_of_isHomogeneous y (isHomogeneous_X k i₀), aeval_X]
      exact hi₀
    · rw [hdim, Cardinal.toENat_eq_natCast.mpr h']
      push_cast
      rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
