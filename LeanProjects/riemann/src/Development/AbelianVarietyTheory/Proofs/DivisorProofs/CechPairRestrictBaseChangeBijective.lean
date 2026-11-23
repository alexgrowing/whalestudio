import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijectiveStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.PairExt

variable {X X' Y : Scheme.{0}}

theorem pair_point (φ : X' ⟶ X) (x : X') (U : X'.Opens) (hx : x ∈ U) :
    ∃ t : (Pair φ)ᵒᵖ, x ∈ ((pairFst φ).obj t).unop.1 ∧ ((pairFst φ).obj t).unop.1 ≤ U := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x) (U := (⊤ : X.Opens)) trivial
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := U ⊓ φ ⁻¹ᵁ V) ⟨hx, hxV⟩
  exact ⟨Opposite.op ⟨(⟨W, hW⟩, ⟨V, hV⟩), fun y hy ↦ (hWU hy).2⟩, hxW, fun y hy ↦ (hWU hy).1⟩

theorem pair_point_two (φ : X' ⟶ X) (t₁ t₂ : (Pair φ)ᵒᵖ) (x : X') (U : X'.Opens) (hx : x ∈ U)
    (h₁ : x ∈ ((pairFst φ).obj t₁).unop.1) (h₂ : x ∈ ((pairFst φ).obj t₂).unop.1) :
    ∃ t₃ : (Pair φ)ᵒᵖ, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((pairFst φ).obj t₃).unop.1 ∧
      ((pairFst φ).obj t₃).unop.1 ≤ U := by
  have h₁' : x ∈ t₁.unop.1.1.1 := h₁
  have h₂' : x ∈ t₂.unop.1.1.1 := h₂
  obtain ⟨V, hV, hxV, hVV⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x)
    (U := t₁.unop.1.2.1 ⊓ t₂.unop.1.2.1) ⟨t₁.unop.2 h₁', t₂.unop.2 h₂'⟩
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x)
    (U := U ⊓ φ ⁻¹ᵁ V ⊓ (t₁.unop.1.1.1 ⊓ t₂.unop.1.1.1)) ⟨⟨hx, hxV⟩, h₁', h₂'⟩
  let t₃ : Pair φ := ⟨(⟨W, hW⟩, ⟨V, hV⟩), fun y hy ↦ (hWU hy).1.2⟩
  refine ⟨Opposite.op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, hxW, fun y hy ↦ (hWU hy).1.1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.1, fun y hy ↦ (hVV hy).1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.2, fun y hy ↦ (hVV hy).2⟩

theorem triple_point (φ : X' ⟶ X) (ψ : X ⟶ Y) (x : X') (U : X'.Opens) (hx : x ∈ U) :
    ∃ t : (Triple φ ψ)ᵒᵖ, x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t).unop.1 ∧
      ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t).unop.1 ≤ U := by
  obtain ⟨Z, hZ, hxZ, -⟩ := exists_isAffineOpen_mem_and_subset (x := ψ.base (φ.base x)) (U := (⊤ : Y.Opens)) trivial
  obtain ⟨V, hV, hxV, hVZ⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x) (U := ψ ⁻¹ᵁ Z) hxZ
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := U ⊓ φ ⁻¹ᵁ V) ⟨hx, hxV⟩
  exact ⟨Opposite.op ⟨(⟨W, hW⟩, ⟨V, hV⟩, ⟨Z, hZ⟩), fun y hy ↦ (hWU hy).2, fun y hy ↦ hVZ hy⟩, hxW,
    fun y hy ↦ (hWU hy).1⟩

theorem triple_point_two (φ : X' ⟶ X) (ψ : X ⟶ Y) (t₁ t₂ : (Triple φ ψ)ᵒᵖ) (x : X') (U : X'.Opens) (hx : x ∈ U)
    (h₁ : x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₁).unop.1)
    (h₂ : x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₂).unop.1) :
    ∃ t₃ : (Triple φ ψ)ᵒᵖ, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧
      x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₃).unop.1 ∧
      ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₃).unop.1 ≤ U := by
  have h₁' : x ∈ t₁.unop.1.1.1 := h₁
  have h₂' : x ∈ t₂.unop.1.1.1 := h₂
  have hy₁ : φ.base x ∈ t₁.unop.1.2.1.1 := t₁.unop.2.1 h₁'
  have hy₂ : φ.base x ∈ t₂.unop.1.2.1.1 := t₂.unop.2.1 h₂'
  obtain ⟨Z, hZ, hxZ, hZZ⟩ := exists_isAffineOpen_mem_and_subset (x := ψ.base (φ.base x))
    (U := t₁.unop.1.2.2.1 ⊓ t₂.unop.1.2.2.1) ⟨t₁.unop.2.2 hy₁, t₂.unop.2.2 hy₂⟩
  obtain ⟨V, hV, hxV, hVV⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x)
    (U := t₁.unop.1.2.1.1 ⊓ t₂.unop.1.2.1.1 ⊓ ψ ⁻¹ᵁ Z) ⟨⟨hy₁, hy₂⟩, hxZ⟩
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x)
    (U := U ⊓ φ ⁻¹ᵁ V ⊓ (t₁.unop.1.1.1 ⊓ t₂.unop.1.1.1)) ⟨⟨hx, hxV⟩, h₁', h₂'⟩
  let t₃ : Triple φ ψ := ⟨(⟨W, hW⟩, ⟨V, hV⟩, ⟨Z, hZ⟩), fun y hy ↦ (hWU hy).1.2, fun y hy ↦ (hVV hy).2⟩
  refine ⟨Opposite.op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, hxW, fun y hy ↦ (hWU hy).1.1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.1, fun y hy ↦ (hVV hy).1.1, fun y hy ↦ (hZZ hy).1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.2, fun y hy ↦ (hVV hy).1.2, fun y hy ↦ (hZZ hy).2⟩

theorem extHom_of_id {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] {B : Type} [CommRing B]
    [Algebra R₀ B] (f : B →ₐ[R₀] B) (hf : ∀ b, f b = b) (y : R₁ ⊗[R₀] B) : extHom R₁ f y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [hf]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem cechTripleRestrict_comp_pairRestrict {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (s' : X' ⟶ Sp R₀)
    (φ : X' ⟶ X) (ψ : X ⟶ Y) (c : CatCoh.H1 (ext R₁ (OAff s'))) :
    (extMap R₁ (cechTripleRestrictFirst φ ψ s')).pull1 ((extMap R₁ (pairRes φ s')).pull1 c) =
      (extMap R₁ (CoefMap.restrict (OAff s') (cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)))).pull1 c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]
  refine congrArg _ (Subtype.ext ?_)
  funext T T' a
  exact extHom_of_id R₁ (coefHom (cechTripleRestrictFirst φ ψ s') T') (fun _ ↦ rfl) _

theorem pairRes_ext_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R₀) (φ : X' ⟶ X), (Function.Bijective (extMap R₁ (pairRes φ s')).pull1 ∧ Function.Bijective (extMap R₁ (pairRes φ s')).pull2) ∧ ∀ (Y : Scheme.{0}) (ψ : X ⟶ Y), Function.Injective (extMap R₁ (cechTripleRestrictFirst φ ψ s')).pull1 := by
  intro R₀ R₁ _ _ _ X X' s' φ
  have hp : Function.Bijective (extMap R₁ (pairRes φ s')).pull1 ∧ Function.Bijective (extMap R₁ (pairRes φ s')).pull2 :=
    GlobalTheory.T.cohomology_restrict_basis_extended_bijective R₀ R₁ X' s' _ (pairFst φ) (pair_point φ) (pair_point_two φ)
  refine ⟨hp, fun Y ψ x y e ↦ ?_⟩
  obtain ⟨x0, rfl⟩ := hp.1.2 x
  obtain ⟨y0, rfl⟩ := hp.1.2 y
  rw [cechTripleRestrict_comp_pairRestrict, cechTripleRestrict_comp_pairRestrict] at e
  rw [(GlobalTheory.T.cohomology_restrict_basis_extended_bijective R₀ R₁ X' s' _ _ (triple_point φ ψ) (triple_point_two φ ψ)).1.1 e]

end GlobalTheory.Obs.PairExt
