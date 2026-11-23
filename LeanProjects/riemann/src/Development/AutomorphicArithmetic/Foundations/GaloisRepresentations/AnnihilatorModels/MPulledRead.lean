import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.pulledRead_of :
    PullKer → PulledRead := by
  intro hKer p _ D R _ b N M r w j c T S x σ o₁ m₁ y hy P a
  have hw : (a.left ≫ P.m₀.φ) ≫ T.o.A.hom = y := by
    have h1 := P.m₀.cart.1.w
    have h2 : a.left ≫ o₁.A.hom = 𝟙 S := Over.w a
    rw [Category.assoc, h1, ← Category.assoc, h2]
    exact Category.id_comp y
  have htri : (a.left ≫ P.m₀.φ) ≫ T.ms.φ = a.left ≫ m₁.φ := by
    rw [Category.assoc, P.tri]
  let a₀ : Over.mk y ⟶ T.o.A := Over.homMk (a.left ≫ P.m₀.φ) hw
  have ha₀ : a₀.left = a.left ≫ P.m₀.φ := rfl
  have hk := ((hKer p D R b N T.Y S (T.s ≫ M.s) σ y T.o T.o' o₁ P.o' P.m₀ P.m' T.ψ P.ψ P.sq).1
    (𝟙_ (Over S)) (Over.mk y) rfl a a₀ (by simp [ha₀])).1
  refine ⟨⟨fun h a' ha' => ?_, fun h => ?_⟩, fun h => ?_⟩
  · have hEq : a' = a₀ := by
      apply Over.OverMorphism.ext
      apply T.ms.cart.1.hom_ext
      · rw [ha', ha₀, htri]
      · have h3 : a'.left ≫ T.o.A.hom = y := Over.w a'
        rw [h3, ha₀, hw]
    rw [hEq]
    exact hk.1 h
  · exact hk.2 (h a₀ (by rw [ha₀, htri]))
  · have hl : T.ms.cart.1.lift (a.left ≫ m₁.φ) y h = a.left ≫ P.m₀.φ := by
      apply T.ms.cart.1.hom_ext
      · rw [T.ms.cart.1.lift_fst, htri]
      · rw [T.ms.cart.1.lift_snd, hw]
    unfold TjD.img
    rw [hl, Over.comp_left]
    simp only [Category.assoc]
    rw [reassoc_of% P.sq]
