import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.JcSmul

theorem valR_const_mul {F A : Type} [Field F] [CommRing A] [Algebra F A] {Y : Scheme.{0}} (r : Sp A ⟶ Y)
    (π : Y ⟶ Sp F) (h : r ≫ π = spMap (algebraMap F A)) (U : Y.Opens) (z : F) (f : Γ(Y, U)) :
    valR r U (resTop U (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z)) * f) =
      algebraMap F A z * valR r U f := by
  unfold valR
  by_cases hU : ⊤ ≤ r ⁻¹ᵁ U
  · rw [dif_pos hU, dif_pos hU, map_mul, map_mul]
    congr 1
    have e : (r.appLE U ⊤ hU).hom (resTop U (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z))) =
        (r ≫ π).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z) := by
      simp only [resTop]
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, Scheme.Hom.comp_appTop,
        CommRingCat.hom_comp, RingHom.comp_apply]
      exact congrArg (fun g : Γ(Y, ⊤) ⟶ Γ(Sp A, ⊤) => g.hom (π.appTop.hom _)) (Scheme.Hom.appLE_eq_app r (U := ⊤))
    rw [e, h]
    have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap F A))
    have := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z)) n
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    simp
  · rw [dif_neg hU, dif_neg hU, mul_zero]

theorem jc_smul : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) {k : ℕ} (s : Fam D F k) (a : F) (gm : GtPt D (TE R F)) (α : N.X),
    jc ν (a • s) gm α = TrivSqZeroExt.inl a * jc ν s gm α := by
  intro R _ _ D F _ _ N ν k s a gm α
  have e : (lift (Over.homMk (spMap (algebraMap F (DualNumber F))) rfl : TE R F ⟶ TF (R := R) F) gm.b).left ≫
      (fst (TF (R := R) F) D.P.A).left = spMap (algebraMap F (DualNumber F)) := by
    rw [← Over.comp_left, lift_fst]
    rfl
  unfold jc sE
  rw [← _root_.mul_assoc]
  congr 1
  have h2 : (TrivSqZeroExt.inl a : DualNumber F) = algebraMap F (DualNumber F) a := rfl
  rw [h2]
  exact valR_const_mul _ _ e _ a _

end GlobalTheory.JcSmul
