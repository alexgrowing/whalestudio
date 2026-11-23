import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

namespace GlobalTheory.FlagCls

theorem universallyInjective_of_fieldPoints {G P : Scheme.{0}} (h : G ⟶ P)
    (H : ∀ (K : Type) [Field K] (z z' : Sp K ⟶ G), z ≫ h = z' ≫ h → z = z') :
    UniversallyInjective h := by
  rw [UniversallyInjective.iff_diagonal, surjective_iff]
  intro x
  let w := (Limits.pullback h h).fromSpecResidueField x
  have e : w ≫ Limits.pullback.fst h h = w ≫ Limits.pullback.snd h h :=
    H ((Limits.pullback h h).residueField x) _ _ (by
      simp only [Category.assoc, Limits.pullback.condition])
  have e2 : (w ≫ Limits.pullback.fst h h) ≫ Limits.pullback.diagonal h = w := by
    apply Limits.pullback.hom_ext
    · simp
    · simp [e]
  let pt : Spec ((Limits.pullback h h).residueField x) := IsLocalRing.closedPoint _
  refine ⟨(w ≫ Limits.pullback.fst h h) pt, ?_⟩
  rw [← Scheme.Hom.comp_apply, e2, Scheme.fromSpecResidueField_apply]

theorem isFinite_of_isProper_of_fieldPoints :
    ∀ (G Y Bg S : Scheme.{0}) (f : G ⟶ Y) (jG : G ⟶ Bg) (πB : Bg ⟶ S) (π : Y ⟶ S), jG ≫ πB = f ≫ π → IsFinite πB → IsProper f → (∀ (K : Type) [Field K] (z z' : Sp K ⟶ G), z ≫ f = z' ≫ f → z ≫ jG = z' ≫ jG → z = z') → IsFinite f := by
  intro G Y Bg S f jG πB π hc hB hf H
  let h : G ⟶ Limits.pullback π πB := Limits.pullback.lift f jG hc.symm
  have e : h ≫ Limits.pullback.fst π πB = f := Limits.pullback.lift_fst _ _ _
  have e' : h ≫ Limits.pullback.snd π πB = jG := Limits.pullback.lift_snd _ _ _
  have hfin : IsFinite (Limits.pullback.fst π πB) := inferInstance
  have : IsProper (h ≫ Limits.pullback.fst π πB) := by rwa [e]
  have : IsProper h := IsProper.of_comp h (Limits.pullback.fst π πB)
  have : UniversallyInjective h := universallyInjective_of_fieldPoints h fun K _ z z' hz =>
    H K z z' (by rw [← e, ← Category.assoc, hz, Category.assoc])
      (by rw [← e', ← Category.assoc, hz, Category.assoc])
  have : IsFinite h := IsFinite.of_isProper_of_locallyQuasiFinite h
  rw [← e]
  infer_instance

end GlobalTheory.FlagCls
