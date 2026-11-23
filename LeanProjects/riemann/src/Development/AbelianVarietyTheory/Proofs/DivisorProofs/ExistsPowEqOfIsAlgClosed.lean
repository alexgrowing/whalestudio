import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedKthRootPullbackBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeMulNFiniteFlatSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDivPt

theorem exists_pow_eq_of_isAlgClosed : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), 0 < n →
      ∀ g : Over.mk x ⟶ A, ∃ g' : Over.mk x ⟶ A, g' ^ n = g := by
  intro S A _ hA k _ _ x n hn g
  have hc := hA.comm
  obtain ⟨hfin, -, hsurj⟩ := GlobalTheory.KthRoot.finite_flat_surjective_mulN_any S A hA n hn
  have : IsFinite (pullback.snd (mulN A n).left g.left) := by
    haveI := hfin; infer_instance
  have : Surjective (pullback.snd (mulN A n).left g.left) := by
    haveI := hsurj; infer_instance
  obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_section (pullback.snd (mulN A n).left g.left)
  have hb' : (t ≫ pullback.fst (mulN A n).left g.left) ≫ (mulN A n).left = g.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  have hw : (t ≫ pullback.fst (mulN A n).left g.left) ≫ A.hom = (Over.mk x).hom := by
    rw [← Over.w (mulN A n), ← Category.assoc, hb', Over.w g]
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : Over.mk x ⟶ A, b ^ n = b ≫ mulN A n := fun b => by
    rw [GlobalTheory.MulFlatSurj.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]
  rw [e]
  exact Over.OverMorphism.ext hb'

end GlobalTheory.AbDivPt
