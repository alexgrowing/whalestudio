import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.imgEq_of :
    ObjTri → ImgEq := by
  intro hTri p _ D R _ b N hN hNp M S s o₁ o₂ t₁ t₂ h₁ h₂ n₁ n₂ m
  obtain ⟨c, hc⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m n₂
  have ht : t₁ = 𝟙 S ≫ t₂ :=
    (M.rep S s o₁).unique ⟨h₁, ⟨n₁⟩⟩ ⟨by rw [Category.id_comp]; exact h₂, ⟨c⟩⟩
  have ht' : t₁ = t₂ := by rw [ht, Category.id_comp]
  refine ⟨ht', ?_⟩
  have key : ∀ f : S ⟶ M.X, f = t₁ → ∀ mm : ObjMap o₁ M.univ f, mm.φ = n₁.φ := by
    intro f hf mm
    subst hf
    exact (hTri p D R b N hN hNp S M.X M.X s M.s M.s o₁ M.univ M.univ f (𝟙 _)).1 mm n₁
  rw [← hc]
  exact key _ ht.symm c
