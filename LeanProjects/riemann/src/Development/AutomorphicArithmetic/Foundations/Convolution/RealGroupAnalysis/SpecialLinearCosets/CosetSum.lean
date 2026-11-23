import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.cosetSum :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (U U' : Subgroup G), U' ≤ U → IsCompact (U : Set G) → IsOpen (U' : Set G) →
      ∃ s : Finset G, s.Nonempty ∧ (∀ g ∈ s, g ∈ U) ∧ ∀ x, ind U x = ∑ g ∈ s, ind U' (x * g⁻¹) := by
  intro G _ _ _ _ U U' hle hU hU'
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have hopen : IsOpen ((U'.subgroupOf U : Subgroup U) : Set U) := hU'.preimage continuous_subtype_val
  haveI : Finite (U ⧸ U'.subgroupOf U) := Subgroup.quotient_finite_of_isOpen _ hopen
  haveI : Finite (Quotient (QuotientGroup.rightRel (U'.subgroupOf U))) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel (U'.subgroupOf U)).symm
  letI : Fintype (Quotient (QuotientGroup.rightRel (U'.subgroupOf U))) := Fintype.ofFinite _
  let mk : U → Quotient (QuotientGroup.rightRel (U'.subgroupOf U)) := fun u => Quotient.mk _ u
  let r : Quotient (QuotientGroup.rightRel (U'.subgroupOf U)) → G := fun q => ((Quotient.out q : U) : G)
  have hrU : ∀ q, r q ∈ U := fun q => (Quotient.out q : U).2
  have hinj : Function.Injective r := by
    intro a b h
    have : (Quotient.out a : U) = Quotient.out b := Subtype.ext h
    rw [← Quotient.out_eq a, ← Quotient.out_eq b, this]
  have key : ∀ (u : U) q, (u : G) * (r q)⁻¹ ∈ U' ↔ q = mk u := by
    intro u q
    have h1 : mk (Quotient.out q) = q := Quotient.out_eq q
    constructor
    · intro h
      rw [← h1]
      refine Quotient.sound ?_
      change QuotientGroup.rightRel _ _ _
      rw [QuotientGroup.rightRel_apply]
      change ((u * (Quotient.out q)⁻¹ : U) : G) ∈ U'
      simpa [r] using h
    · intro h
      have h2 : mk (Quotient.out q) = mk u := h1.trans h
      have h3 := Quotient.exact h2
      change QuotientGroup.rightRel _ _ _ at h3
      rw [QuotientGroup.rightRel_apply] at h3
      have h4 : ((u * (Quotient.out q)⁻¹ : U) : G) ∈ U' := h3
      simpa [r] using h4
  refine ⟨Finset.univ.image r, ⟨r (mk 1), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, ?_, ?_⟩
  · intro g hg
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hg
    exact hrU q
  · intro x
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    by_cases hx : x ∈ U
    · have h1 : ind U x = 1 := by simp [ind, Set.indicator, hx]
      rw [h1, Finset.sum_eq_single (mk ⟨x, hx⟩)]
      · have : x * (r (mk ⟨x, hx⟩))⁻¹ ∈ U' := (key ⟨x, hx⟩ _).mpr rfl
        simp [ind, Set.indicator, this]
      · intro q _ hq
        have : x * (r q)⁻¹ ∉ U' := fun h => hq ((key ⟨x, hx⟩ q).mp h)
        simp [ind, Set.indicator, this]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have h1 : ind U x = 0 := by simp [ind, Set.indicator, hx]
      rw [h1]
      symm
      refine Finset.sum_eq_zero fun q _ => ?_
      have : x * (r q)⁻¹ ∉ U' := fun h => hx (by
        have := U.mul_mem (hle h) (hrU q)
        simpa using this)
      simp [ind, Set.indicator, this]
