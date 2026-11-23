import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtAlong
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationSectionFirstPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPullbackNonvanishingOfPulledSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationSectionNthPowerDescends
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TranslateSection

theorem translT_inv_comp {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (z : T ⟶ A) :
    translT A z⁻¹ ≫ translT A z = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp only [translT, translPt, Category.assoc, lift_snd, lift_fst, Category.id_comp, comp_lift_assoc, lift_fst_assoc]
    change (fst T A ≫ z) * ((fst T A ≫ z⁻¹) * snd T A) = snd T A
    have e : fst T A ≫ z⁻¹ = (fst T A ≫ z)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one])
    rw [e, mul_inv_cancel_left]

theorem translT_surjective : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (z : T ⟶ A), Function.Surjective (translT A z).left.base := by
  intro S A _ T z y
  refine ⟨(translT A z⁻¹).left.base y, ?_⟩
  have h := congrArg (fun f : T ⊗ A ⟶ T ⊗ A => f.left y) (translT_inv_comp A z)
  simpa [Scheme.Hom.comp_apply] using h

theorem mulT_eq {S : Scheme.{0}} (A : Over S) [GrpObj A] (m : ℕ) :
    mulT A (baseOver S) m = (λ_ A).hom ≫ mulA A m ≫ (λ_ A).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv, CartesianMonoidalCategory.leftUnitor_hom, mulT]
  refine (lift_snd _ _).trans ?_
  rw [mulA, MonObj.comp_pow, Category.comp_id]
  rfl

theorem mulT_surjective : ∀ {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (m : ℕ), 1 ≤ m → Function.Surjective (mulT P.A (baseOver S) m).left.base := by
  intro S _ P m hm y
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨-, -, hs, -⟩ := hLaw.mulN S P m hm
  obtain ⟨b, hb⟩ := hs.surj ((λ_ P.A).hom.left y)
  refine ⟨(λ_ P.A).inv.left b, ?_⟩
  have h1 := congrArg (fun f : baseOver S ⊗ P.A ⟶ baseOver S ⊗ P.A => f.left ((λ_ P.A).inv.left b)) (mulT_eq P.A m)
  have h2 := congrArg (fun f : baseOver S ⊗ P.A ⟶ baseOver S ⊗ P.A => f.left y) (λ_ P.A).hom_inv_id
  have h3 := congrArg (fun f : P.A ⟶ P.A => f.left b) (λ_ P.A).inv_hom_id
  simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.id_left] at h1 h2 h3
  have h2' : (λ_ P.A).inv.left ((λ_ P.A).hom.left y) = y := h2
  have h3' : (λ_ P.A).hom.left ((λ_ P.A).inv.left b) = b := h3
  rw [h1, h3', hb, h2']

theorem mem_nonzeroLocus_of_isTwistPull : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}, L.IsLB → ∀ {T : Over S} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)), IsTwistPull A L ψ m hm a b α s s' → ∀ p : (T ⊗ A).left, ψ.left.base p ∈ nonzeroLocus s → p ∈ nonzeroLocus s' := GlobalTheory.T.twistedPullback_nonvanishing_of_pulledSection

end GlobalTheory.MBLow.TranslateSection
