import Development.EtaleCohomology.EtaleSheaves.LeafNormalModelPf
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral

noncomputable section
open Polynomial

namespace LateralTheory.E.LeafIntClosureAlgPf
open LateralTheory.E.LeafNormalModelPf

variable {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L]

theorem isAlgebraic_of_mem_adjoin (u x : L) (hx : x ∈ IntermediateField.adjoin Ω {u}) :
    IsAlgebraic (Algebra.adjoin Ω {u}) x := by
  obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff (F := Ω) (α := u) x).1 hx
  set R := Algebra.adjoin Ω {u}
  have hr : aeval u r ∈ R := by rw [show R = _ from Algebra.adjoin_singleton_eq_range_aeval Ω u]; exact ⟨r, rfl⟩
  have hs : aeval u s ∈ R := by rw [show R = _ from Algebra.adjoin_singleton_eq_range_aeval Ω u]; exact ⟨s, rfl⟩
  by_cases h0 : aeval u s = 0
  · rw [h0, div_zero]; exact isAlgebraic_zero
  refine ⟨C (⟨aeval u s, hs⟩ : R) * X - C ⟨aeval u r, hr⟩, ?_, ?_⟩
  · intro h
    have := congrArg (fun p => p.coeff 1) h
    simp only [coeff_sub, coeff_C_mul, coeff_X_one, mul_one, coeff_C, one_ne_zero, if_false,
      sub_zero, coeff_zero] at this
    exact h0 (congrArg Subtype.val this)
  · simp only [map_sub, map_mul, aeval_C, aeval_X]
    change aeval u s * (aeval u r / aeval u s) - aeval u r = 0
    rw [mul_div_cancel₀ _ h0, sub_self]

variable (Ω) in
theorem isAlgebraic_adjoin (u : L) [FiniteDimensional (IntermediateField.adjoin Ω {u}) L] :
    Algebra.IsAlgebraic (Algebra.adjoin Ω {u}) L := by
  constructor
  intro z
  set K := IntermediateField.adjoin Ω {u}
  have h1 : IsAlgebraic K z := Algebra.IsAlgebraic.isAlgebraic z
  have h2 : IsAlgebraic K.toSubalgebra z := h1
  have h3 : IsAlgebraic (Algebra.adjoin Ω (K : Set L)) z :=
    h2.tower_top_of_subalgebra_le (fun y hy => Algebra.subset_adjoin hy)
  refine IsAlgebraic.adjoin_of_forall_isAlgebraic (fun y hy => ?_) h3
  exact isAlgebraic_of_mem_adjoin u y hy.1

variable (Ω) in
theorem isFractionRing_intClosure (u : L) [FiniteDimensional (IntermediateField.adjoin Ω {u}) L] :
    IsFractionRing (integralClosure (Algebra.adjoin Ω {u}) L) L := by
  have := isAlgebraic_adjoin Ω u
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨y, hy, hint⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := Algebra.adjoin Ω {u}) z).exists_integral_multiple
  have hy' : (y : L) ≠ 0 := fun h => hy (Subtype.ext h)
  refine ⟨⟨y • z, hint⟩, ⟨(y : L), isIntegral_algebraMap (R := Algebra.adjoin Ω {u}) (x := y)⟩, ?_⟩
  change z = y • z / (y : L)
  rw [Algebra.smul_def]
  change z = (y : L) * z / (y : L)
  field_simp

variable (Ω) in
theorem isIntegrallyClosed_intClosure (u : L) [FiniteDimensional (IntermediateField.adjoin Ω {u}) L] :
    IsIntegrallyClosed (integralClosure (Algebra.adjoin Ω {u}) L) := by
  have := isFractionRing_intClosure Ω u
  rw [isIntegrallyClosed_iff L]
  intro x hx
  exact ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩

theorem ringKrullDim_intClosure (u : L) (hu : Transcendental Ω u) :
    ringKrullDim (integralClosure (Algebra.adjoin Ω {u}) L) = 1 := by
  have h1 := ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (A := Algebra.adjoin Ω {u})
    (B := integralClosure (Algebra.adjoin Ω {u}) L) (fun a b h => Subtype.ext (congrArg (Subtype.val : integralClosure (Algebra.adjoin Ω {u}) L → L) h))
  have h2 := ringKrullDim_eq_of_ringEquiv (Polynomial.algEquivOfTranscendental Ω u hu).toRingEquiv
  rw [h1, ← h2]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one _ (Polynomial.not_isField Ω)

def LeafIntClFinite : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    Module.Finite (Algebra.adjoin Ω {u}) (integralClosure (Algebra.adjoin Ω {u}) L)

theorem finiteType_intCl (u : L) (h : Module.Finite (Algebra.adjoin Ω {u}) (integralClosure (Algebra.adjoin Ω {u}) L)) :
    Algebra.FiniteType Ω (intCl Ω u) := by
  have h1 : Algebra.FiniteType Ω (Algebra.adjoin Ω {u}) :=
    (Subalgebra.fg_iff_finiteType _).1 ⟨{u}, by rw [Finset.coe_singleton]⟩
  have h2 : Algebra.FiniteType (Algebra.adjoin Ω {u}) (integralClosure (Algebra.adjoin Ω {u}) L) := inferInstance
  have h3 : Algebra.FiniteType Ω (integralClosure (Algebra.adjoin Ω {u}) L) :=
    Algebra.FiniteType.trans (S := Algebra.adjoin Ω {u}) h1 h2
  exact h3

theorem LeafIntClosureAlg_of (h : LeafIntClFinite) : LeafIntClosureAlg := by
  intro Ω L _ _ _ u hu hfd
  refine ⟨finiteType_intCl u (h Ω L u hu hfd), ?_, ?_, ?_⟩
  · exact isIntegrallyClosed_intClosure Ω u
  · exact ringKrullDim_intClosure u hu
  · exact isFractionRing_intClosure Ω u

end LateralTheory.E.LeafIntClosureAlgPf
