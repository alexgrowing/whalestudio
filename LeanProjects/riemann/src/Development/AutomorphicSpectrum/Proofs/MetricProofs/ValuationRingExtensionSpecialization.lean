import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.ComplexPlace

theorem exists_ringHom_of_finiteType {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (v : A →+* ℂ) (hv : (RingHom.ker v).IsMaximal) (M : Ideal B)
    (hMm : M.IsMaximal) (hM : ∀ a, v a = 0 → algebraMap A B a ∈ M) :
    ∃ ψ : B →+* ℂ, ∀ a, ψ (algebraMap A B a) = v a := by
  letI κF : Field (A ⧸ RingHom.ker v) := Ideal.Quotient.field _
  letI KF : Field (B ⧸ M) := Ideal.Quotient.field _
  let φ : A ⧸ RingHom.ker v →+* B ⧸ M :=
    Ideal.quotientMap M (algebraMap A B) (fun a ha => hM a (RingHom.mem_ker.mp ha))
  letI : Algebra (A ⧸ RingHom.ker v) (B ⧸ M) := φ.toAlgebra
  haveI : IsScalarTower A (A ⧸ RingHom.ker v) (B ⧸ M) :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : Algebra.FiniteType A (B ⧸ M) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A M) (Ideal.Quotient.mkₐ_surjective A M)
  haveI : Algebra.FiniteType (A ⧸ RingHom.ker v) (B ⧸ M) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ RingHom.ker v) (B ⧸ M)
  haveI : Module.Finite (A ⧸ RingHom.ker v) (B ⧸ M) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  letI : Algebra (A ⧸ RingHom.ker v) ℂ := (RingHom.kerLift v).toAlgebra
  let g : (B ⧸ M) →ₐ[A ⧸ RingHom.ker v] ℂ := IsAlgClosed.lift
  refine ⟨g.toRingHom.comp (Ideal.Quotient.mk M), fun a => ?_⟩
  exact g.commutes (Ideal.Quotient.mk (RingHom.ker v) a)

theorem isLocalRing_and_ker {L : Type} [Field L] (O : Subring L) (v : O →+* ℂ)
    (hv : ∀ s : O, v s ≠ 0 → (s : L)⁻¹ ∈ O) :
    ∃ _ : IsLocalRing O, RingHom.ker v = IsLocalRing.maximalIdeal O := by
  have hunit : ∀ s : O, IsUnit s ↔ v s ≠ 0 := by
    intro s
    constructor
    · intro h
      exact (h.map v).ne_zero
    · intro h
      have hs : (s : L) ≠ 0 := by
        intro h0
        apply h
        have : s = 0 := Subtype.ext h0
        simp [this]
      refine IsUnit.of_mul_eq_one (⟨(s : L)⁻¹, hv s h⟩ : O) ?_
      exact Subtype.ext (mul_inv_cancel₀ hs)
  have hloc : IsLocalRing O := by
    refine IsLocalRing.of_nonunits_add ?_
    intro a b ha hb
    have ha' : v a = 0 := by
      by_contra h
      exact ha ((hunit a).2 h)
    have hb' : v b = 0 := by
      by_contra h
      exact hb ((hunit b).2 h)
    intro hab
    exact (hunit _).1 hab (by simp [ha', hb'])
  refine ⟨hloc, ?_⟩
  ext s
  rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
  simp

theorem exists_valuationSubring_place (L : Type) [Field L] (O : Subring L) (v : O →+* ℂ)
    (hv : ∀ s : O, v s ≠ 0 → (s : L)⁻¹ ∈ O) :
    ∃ V : ValuationSubring L, (∀ s ∈ O, s ∈ V) ∧ ∀ T : Finset L, (∀ t ∈ T, t ∈ V) →
      ∃ (R : Subring L) (hO : O ≤ R) (ψ : R →+* ℂ), (∀ t ∈ T, t ∈ R) ∧
        (∀ s : O, ψ (Subring.inclusion hO s) = v s) ∧ ∀ t ∈ T, t ≠ 0 → t⁻¹ ∈ V → t⁻¹ ∈ R := by
  obtain ⟨hloc, hker⟩ := isLocalRing_and_ker O v hv
  obtain ⟨V, hV, hlocal⟩ := IsLocalRing.exists_factor_valuationRing O.subtype
  refine ⟨V, fun s hs => hV ⟨s, hs⟩, fun T hT => ?_⟩
  let S : Finset L := T ∪ (T.filter (fun t => t⁻¹ ∈ V)).image (fun t => t⁻¹)
  have hSV : ∀ x ∈ S, x ∈ V := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hT x h
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp ht).2
  let B : Subalgebra O L := Algebra.adjoin O (S : Set L)
  let VA : Subalgebra O L :=
    { V.toSubring with algebraMap_mem' := fun s => hV s }
  have hBV : B ≤ VA := Algebra.adjoin_le (fun x hx => hSV x hx)
  haveI : Algebra.FiniteType O B :=
    (Subalgebra.fg_iff_finiteType B).1 (Subalgebra.fg_adjoin_finset S)
  let f : B →+* V :=
    { toFun := fun x => ⟨x.1, hBV x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let n : Ideal B := (IsLocalRing.maximalIdeal V).comap f
  have hn : n ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ n := h ▸ Submodule.mem_top
    have h2 : f 1 ∈ IsLocalRing.maximalIdeal V := h1
    rw [map_one] at h2
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal V).ne_top h2
  obtain ⟨M, hMm, hnM⟩ := Ideal.exists_le_maximal n hn
  have hM : ∀ a : O, v a = 0 → algebraMap O B a ∈ M := by
    intro a ha
    apply hnM
    have ha' : a ∈ IsLocalRing.maximalIdeal O := hker ▸ RingHom.mem_ker.mpr ha
    show f (algebraMap O B a) ∈ IsLocalRing.maximalIdeal V
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha' ⊢
    intro hu
    apply ha'
    exact hlocal.map_nonunit a hu
  have hvm : (RingHom.ker v).IsMaximal := by
    rw [hker]
    exact IsLocalRing.maximalIdeal.isMaximal O
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_finiteType v hvm M hMm hM
  have hO : O ≤ B.toSubring := fun s hs => B.algebraMap_mem (⟨s, hs⟩ : O)
  refine ⟨B.toSubring, hO, ψ, ?_, ?_, ?_⟩
  · intro t ht
    exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_left _ ht))
  · intro s
    exact hψ s
  · intro t ht _ hi
    exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨t, Finset.mem_filter.2 ⟨ht, hi⟩, rfl⟩)))

end GlobalTheory.CompanionTheory.Ar.ComplexPlace
