import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCMFieldOfForallIsConj

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.CMSub

section Crit

open ComplexEmbedding InfinitePlace IntermediateField

theorem isCMField_of_forall_isConj (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    {σ : K ≃ₐ[ℚ] K} (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) : IsCMField K := by
  first
  | exact @_root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj
  | exact _root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj
  | (apply _root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj <;> assumption)
  | (intros; apply _root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj ..)

end Crit

def conjStable (Ω : Type) [Field Ω] : Subfield Ω where
  carrier := {x | ∃ y : Ω, ∀ φ : Ω →+* ℂ, φ y = starRingEnd ℂ (φ x)}
  mul_mem' := by
    rintro a b ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨y * z, fun φ => by simp [hy, hz]⟩
  one_mem' := ⟨1, fun φ => by simp⟩
  add_mem' := by
    rintro a b ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨y + z, fun φ => by simp [hy, hz]⟩
  zero_mem' := ⟨0, fun φ => by simp⟩
  neg_mem' := by
    rintro a ⟨y, hy⟩
    exact ⟨-y, fun φ => by simp [hy]⟩
  inv_mem' := by
    rintro a ⟨y, hy⟩
    exact ⟨y⁻¹, fun φ => by simp [hy]⟩

variable {Ω : Type} [Field Ω] {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω]

theorem nonempty_ringHom_complex (E Ω : Type) [Field Ω] [Field E] [NumberField E] [Algebra E Ω]
    [IsAlgClosure E Ω] : Nonempty (Ω →+* ℂ) := by
  let ψ : E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  letI : Algebra E ℂ := ψ.toAlgebra
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  exact ⟨(IsAlgClosed.lift : Ω →ₐ[E] ℂ).toRingHom⟩

theorem exists_extend (M : IntermediateField E Ω) (ψ : M →+* ℂ) :
    ∃ φ : Ω →+* ℂ, ∀ x : M, φ x = ψ x := by
  letI : Algebra M ℂ := ψ.toAlgebra
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic M Ω := Algebra.IsAlgebraic.tower_top (K := E) M
  let f : Ω →ₐ[M] ℂ := IsAlgClosed.lift
  exact ⟨f.toRingHom, fun x => f.commutes x⟩

theorem mem_of_conj {L : IntermediateField E Ω} {x y : Ω} (hx : x ∈ L)
    (hy : ∀ φ : Ω →+* ℂ, φ y = starRingEnd ℂ (φ x)) : y ∈ L := by
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  obtain ⟨φ₀⟩ := nonempty_ringHom_complex E Ω
  rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
  intro τ hτ
  have hτx : τ x = x := (mem_fixingSubgroup_iff _).mp hτ x hx
  apply φ₀.injective
  have h1 : φ₀ (τ y) = starRingEnd ℂ (φ₀ (τ x)) := hy (φ₀.comp τ.toRingHom)
  rw [h1, hτx, hy φ₀]

theorem algebraMap_mem_conjStable [IsCMField E] (e : E) : algebraMap E Ω e ∈ conjStable Ω :=
  ⟨algebraMap E Ω (IsCMField.complexConj E e), fun φ =>
    IsCMField.complexEmbedding_complexConj E (φ.comp (algebraMap E Ω)) e⟩

def conjField (E Ω : Type) [Field Ω] [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] :
    IntermediateField E Ω :=
  (conjStable Ω).toIntermediateField algebraMap_mem_conjStable

theorem le_conjField [IsCMField E] (M : IntermediateField E Ω) [NumberField M] [IsCMField M] :
    M ≤ conjField E Ω := fun x hx =>
  ⟨(IsCMField.complexConj M ⟨x, hx⟩ : M), fun φ =>
    IsCMField.complexEmbedding_complexConj M (φ.comp (algebraMap M Ω)) ⟨x, hx⟩⟩

theorem isCMField_of_le [IsCMField E] (M : IntermediateField E Ω) [NumberField M]
    (h : M ≤ conjField E Ω) : IsCMField M := by
  haveI : IsTotallyComplex M := isTotallyComplex_of_algebra E M
  have hc : ∀ x : M, ∃ y : M, ∀ φ : Ω →+* ℂ, φ y = starRingEnd ℂ (φ x) := fun x => by
    obtain ⟨y, hy⟩ := h x.2
    exact ⟨⟨y, mem_of_conj x.2 hy⟩, hy⟩
  choose c hc using hc
  obtain ⟨φ₀⟩ := nonempty_ringHom_complex E Ω
  have inj : ∀ a b : M, φ₀ a = φ₀ b → a = b := fun a b hab => Subtype.ext (φ₀.injective hab)
  let f : M →+* M :=
    { toFun := c
      map_one' := inj _ _ (by simp [hc])
      map_mul' := fun a b => inj _ _ (by simp [hc])
      map_zero' := inj _ _ (by simp [hc])
      map_add' := fun a b => inj _ _ (by simp [hc]) }
  have hff : ∀ x, c (c x) = x := fun x => inj _ _ (by simp [hc])
  let g : M ≃+* M := RingEquiv.ofRingHom f f (by ext x; exact congrArg Subtype.val (hff x))
    (by ext x; exact congrArg Subtype.val (hff x))
  let σ : M ≃ₐ[ℚ] M := AlgEquiv.ofRingEquiv (f := g) (fun q => by
    rw [eq_ratCast (algebraMap ℚ M) q, map_ratCast])
  refine isCMField_of_forall_isConj M (σ := σ) fun ψ => ?_
  obtain ⟨φ, hφ⟩ := exists_extend M ψ
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply]
  have e1 : ((σ : M →+* M) x) = c x := rfl
  rw [e1, ← hφ, ← hφ, hc]

theorem isCMField_sup_le_adjoin : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω], (∀ (M N : IntermediateField E Ω) [NumberField M] [NumberField N] [NumberField ↥(M ⊔ N)], IsCMField M → IsCMField N → IsCMField ↥(M ⊔ N)) ∧ (∀ (M N : IntermediateField E Ω) [NumberField M] [NumberField N], N ≤ M → IsCMField M → IsCMField N) ∧ ∀ (M : IntermediateField E Ω) [NumberField M] (S : Set Ω), (∀ x ∈ S, ∀ φ : Ω →+* ℂ, (φ x).im = 0) → M = IntermediateField.adjoin E S → IsCMField M := by
  intro Ω _ E _ _ _ _ _
  refine ⟨fun M N _ _ _ hM hN => isCMField_of_le _ (sup_le (le_conjField M) (le_conjField N)),
    fun M N _ _ hNM hM => isCMField_of_le _ (hNM.trans (le_conjField M)),
    fun M _ S hS hMS => isCMField_of_le _ ?_⟩
  rw [hMS, IntermediateField.adjoin_le_iff]
  intro x hx
  exact ⟨x, fun φ => (Complex.conj_eq_iff_im.mpr (hS x hx φ)).symm⟩

end GlobalTheory.CMSub

end
