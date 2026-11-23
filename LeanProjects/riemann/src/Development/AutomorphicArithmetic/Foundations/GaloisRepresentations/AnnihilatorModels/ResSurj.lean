import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private noncomputable abbrev resU {V : Type} [CommRing V] [IsDomain V] {S : Scheme.{0}} (z : Sp V ⟶ S) :
    Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ Over.mk z :=
  Over.homMk (spMap (algebraMap V (FractionRing V))) rfl

private theorem res_inj (hV : ValPtsX) {S : Scheme.{0}} {A : Over S} (hA : IsProper A.hom)
    {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] (z : Sp V ⟶ S) {g g' : Over.mk z ⟶ A}
    (e : resU z ≫ g = resU z ≫ g') : g = g' := by
  apply Over.OverMorphism.ext
  have e' := congrArg CommaMorphism.left e
  simp only [Over.comp_left, Over.homMk_left] at e'
  exact (hV S A.left A.hom hA V z).1 g.left g'.left (by simpa using Over.w g)
    (by simpa using Over.w g') e'

private theorem res_surj (hV : ValPtsX) {S : Scheme.{0}} {A : Over S} (hA : IsProper A.hom)
    {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] (z : Sp V ⟶ S)
    (g : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ A) :
    ∃ g' : Over.mk z ⟶ A, resU z ≫ g' = g := by
  obtain ⟨l, h₁, h₂⟩ := (hV S A.left A.hom hA V z).2 g.left (by simpa using Over.w g)
  exact ⟨Over.homMk l h₁, Over.OverMorphism.ext h₂⟩

theorem UpperTheory.Gal.crystallineComparison.Mod.wVal_of :
    ValPtsX → WVal := by
  intro hV p _ D R _ b N M w V _ _ _ x
  have hU : IsProper M.univ.A.hom := @IsAbelianScheme.proper _ M.univ.A M.univ.grp M.univ.ab
  let φ : (Over.mk x ⟶ M.univ.A) →* (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x) ⟶ M.univ.A) :=
    { toFun := fun g => resU x ≫ g
      map_one' := comp_one _
      map_mul' := fun g h => comp_mul _ g h }
  let ρ := MulEquiv.ofBijective φ
    ⟨fun g g' e => res_inj hV hU x e, fun g => res_surj hV hU x g⟩
  have hρ : ∀ g, ρ g = resU x ≫ g := fun _ => rfl
  refine ⟨ρ, ?_⟩
  simp only [hρ]
  refine ⟨fun g => by simp, fun g a => (Category.assoc _ _ _).symm, fun g => ?_, ?_⟩
  · constructor
    · intro hg a ha
      rw [Category.assoc, hg a ha, comp_one]
    · intro hg a ha
      apply res_inj hV hU x
      rw [comp_one, ← Category.assoc]
      exact hg a ha
  · intro r j c T z hz g
    have hO : IsProper T.o.A.hom := @IsAbelianScheme.proper _ T.o.A T.o.grp T.o.ab
    have hO' : IsProper T.o'.A.hom := @IsAbelianScheme.proper _ T.o'.A T.o'.grp T.o'.ab
    constructor
    · intro hk b' hb'
      obtain ⟨a', ha'⟩ := res_surj hV hO z b'
      have ha2 := congrArg CommaMorphism.left ha'
      simp only [Over.comp_left, Over.homMk_left] at ha2
      have hb2 : b'.left ≫ T.ms.φ = spMap (algebraMap V (FractionRing V)) ≫ g.left := by
        simpa using hb'
      have hw : (a'.left ≫ T.ms.φ) ≫ M.univ.A.hom = (Over.mk x).hom := by
        rw [Category.assoc, T.ms.cart.1.w, ← Category.assoc, Over.w a']
        exact hz
      have key : (Over.homMk (a'.left ≫ T.ms.φ) hw : Over.mk x ⟶ M.univ.A) = g := by
        apply res_inj hV hU x
        apply Over.OverMorphism.ext
        simp only [Over.comp_left, Over.homMk_left]
        rw [← Category.assoc, ha2, hb2]
      have hg : a'.left ≫ T.ms.φ = g.left := by
        rw [← key]
        simp
      rw [← ha', Category.assoc, hk a' hg, comp_one]
    · intro hk a' ha'
      apply res_inj hV hO' z
      rw [comp_one, ← Category.assoc]
      apply hk
      simp [ha']
