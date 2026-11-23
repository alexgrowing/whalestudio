import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.etInj_of :
    ObjTri → LevPull → EtInj := by
  intro hTri hPull p _ D R _ b N h3 hc M 𝔞 ρ E π hπ mπ X u v huv hlv
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N E.X X E.s u E.univ
  obtain ⟨l, hl, hlu⟩ := hPull p D R b N E.X X E.s (u ≫ E.s) u E.univ o₁ m₁ 𝔞 ρ E.lv E.isLev
  obtain ⟨m₁₃, hm₁₃⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₁ mπ
  obtain ⟨m₂, hm₂⟩ := (hTri p D R b N h3 hc X E.X M.X (u ≫ E.s) E.s M.s o₁ E.univ M.univ v π).2
    (u ≫ π) huv.symm m₁₃ mπ
  have hvs : v ≫ E.s = u ≫ E.s := by
    rw [← hπ, ← Category.assoc, ← Category.assoc, huv]
  have hsec : ∀ y, (l y).left ≫ o₁.A.hom = 𝟙 X := fun y => by
    simpa using Over.w (l y)
  have hsec' : ∀ y, (E.lv y).left ≫ E.univ.A.hom = 𝟙 E.X := fun y => by
    simpa using Over.w (E.lv y)
  have hlv₂ : ∀ y, (l y).left ≫ m₂.φ = v ≫ (E.lv y).left := fun y => by
    refine mπ.cart.1.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [hm₂, hm₁₃, ← Category.assoc, hlu y, Category.assoc, hlv y]
    · simp only [Category.assoc]
      rw [m₂.cart.1.w, ← Category.assoc, hsec, hsec', Category.comp_id]
      exact Category.id_comp v
  exact (E.rep X _ o₁ l hl).unique ⟨rfl, m₁, hlu⟩ ⟨hvs, m₂, hlv₂⟩
