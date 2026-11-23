import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentation

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.IdemSplit

section General

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : C} [GrpObj G]
  (i : H ⟶ G) (r : G ⟶ H) (hir : i ≫ r = 𝟙 H) [he : IsMonHom (r ≫ i)]

include hir in
theorem sec_idem : i ≫ r ≫ i = i := by rw [reassoc_of% hir]

theorem one_comp : (η[G] ≫ r) ≫ i = η[G] := by
  rw [Category.assoc, IsMonHom.one_hom]

include hir in
theorem mul_comp : ((i ⊗ₘ i) ≫ μ[G] ≫ r) ≫ i = (i ⊗ₘ i) ≫ μ[G] := by
  rw [Category.assoc, Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
    sec_idem i r hir]

include hir in
theorem inv_comp : (i ≫ GrpObj.inv ≫ r) ≫ i = i ≫ GrpObj.inv := by
  rw [Category.assoc, Category.assoc, GrpObj.inv_hom, ← Category.assoc, sec_idem i r hir]

@[reducible] def grpObj : GrpObj H :=
  haveI : Mono i := (SplitMono.mk r hir).mono
  { one := η[G] ≫ r
    mul := (i ⊗ₘ i) ≫ μ[G] ≫ r
    one_mul := by
      rw [← cancel_mono i, Category.assoc, mul_comp i r hir, ← tensorHom_id,
        tensorHom_comp_tensorHom_assoc, one_comp, Category.id_comp, tensorHom_def'_assoc,
        MonObj.one_mul, leftUnitor_naturality]
    mul_one := by
      rw [← cancel_mono i, Category.assoc, mul_comp i r hir, ← id_tensorHom,
        tensorHom_comp_tensorHom_assoc, one_comp, Category.id_comp, tensorHom_def_assoc,
        MonObj.mul_one, rightUnitor_naturality]
    mul_assoc := by
      rw [← cancel_mono i, Category.assoc, Category.assoc (α_ H H H).hom, Category.assoc (H ◁ _),
        mul_comp i r hir, ← id_tensorHom, ← tensorHom_id,
        tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, mul_comp i r hir,
        Category.id_comp]
      have h1 : ((i ⊗ₘ i) ≫ μ[G]) ⊗ₘ i = ((i ⊗ₘ i) ⊗ₘ i) ≫ μ[G] ▷ G := by
        rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
      have h2 : i ⊗ₘ ((i ⊗ₘ i) ≫ μ[G]) = (i ⊗ₘ (i ⊗ₘ i)) ≫ G ◁ μ[G] := by
        rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
      rw [h1, h2, Category.assoc, Category.assoc, MonObj.mul_assoc, associator_naturality_assoc]
    inv := i ≫ GrpObj.inv ≫ r
    left_inv := by
      rw [← cancel_mono i, Category.assoc, Category.assoc (toUnit H), mul_comp i r hir, one_comp,
        lift_map_assoc, inv_comp i r hir, Category.id_comp]
      have := GrpObj.left_inv G
      have h2 := congrArg (i ≫ ·) this
      simpa using h2
    right_inv := by
      rw [← cancel_mono i, Category.assoc, Category.assoc (toUnit H), mul_comp i r hir, one_comp,
        lift_map_assoc, inv_comp i r hir, Category.id_comp]
      have := GrpObj.right_inv G
      have h2 := congrArg (i ≫ ·) this
      simpa using h2 }

theorem isMonHom_sec : letI := grpObj i r hir; IsMonHom i :=
  letI := grpObj i r hir
  { one_hom := one_comp i r
    mul_hom := mul_comp i r hir }

theorem isMonHom_ret : letI := grpObj i r hir; IsMonHom r :=
  letI := grpObj i r hir
  { one_hom := rfl
    mul_hom := by
      haveI : Mono i := (SplitMono.mk r hir).mono
      change μ[G] ≫ r = (r ⊗ₘ r) ≫ (i ⊗ₘ i) ≫ μ[G] ≫ r
      rw [← cancel_mono i, Category.assoc, Category.assoc (r ⊗ₘ r), mul_comp i r hir,
        tensorHom_comp_tensorHom_assoc, IsMonHom.mul_hom] }

theorem isComm [BraidedCategory C] [IsCommMonObj G] : letI := grpObj i r hir; IsCommMonObj H :=
  letI := grpObj i r hir
  { mul_comm := by
      change (β_ H H).hom ≫ (i ⊗ₘ i) ≫ μ[G] ≫ r = (i ⊗ₘ i) ≫ μ[G] ≫ r
      rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc] }

end General

end GlobalTheory.SS.IdemSplit

namespace GlobalTheory.SS

theorem smConn_idempotent_splits : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], SmConn G → ∀ e : G ⟶ G, IsMonHom e → e ≫ e = e → ∃ (G₁ : Over S) (_ : GrpObj G₁) (i : G₁ ⟶ G) (r : G ⟶ G₁), SmConn G₁ ∧ IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 G₁ ∧ r ≫ i = e := by
  intro S G _ hG e he hee
  obtain ⟨hc, hs, hsep, hqc, hgc⟩ := hG
  let i := equalizer.ι e (𝟙 G)
  let r : G ⟶ equalizer e (𝟙 G) := equalizer.lift e (by simp [hee])
  have hri : r ≫ i = e := equalizer.lift_ι _ _
  have hir : i ≫ r = 𝟙 _ := by
    rw [← cancel_mono i, Category.assoc, hri, Category.id_comp]
    simpa using equalizer.condition e (𝟙 G)
  haveI : IsMonHom (r ≫ i) := by rw [hri]; exact he
  have hl : i.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, hir, Over.id_left]
  have hw := Over.w r
  exact ⟨_, IdemSplit.grpObj i r hir, i, r,
    ⟨IdemSplit.isComm i r hir, GlobalTheory.Retract.smooth hl hw, GlobalTheory.Retract.isSeparated hl hw,
      GlobalTheory.Retract.quasiCompact hl hw, GlobalTheory.Retract.geometricallyConnected hl hw⟩,
    IdemSplit.isMonHom_sec i r hir, IdemSplit.isMonHom_ret i r hir, hir, hri⟩

end GlobalTheory.SS
