import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.finModel_holds :
    FinCover → FinModel := by
  intro cover p _ D R _ _ b N h3 hcop 𝔞 r h𝔞 M
  haveI : Smooth M.s := M.smooth.smooth
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨Y, q, u, mu, lev, act, hlev, hgal, hrep⟩ :=
    cover p D R b N 𝔞 r h3 hcop h𝔞 M.X M.s M.univ
  let E : EtModel b N 𝔞 r :=
    { X := Y, s := q ≫ M.s, univ := u, lv := lev, isLev := hlev
      rep := by
        intro T t o l hl
        obtain ⟨c, ⟨hc, ⟨mc⟩⟩, cuniq⟩ := M.rep T t o
        subst hc
        obtain ⟨f, ⟨hfq, m₂, hm₂⟩, funiq⟩ := hrep T c o mc l hl
        refine ⟨f, ⟨?_, m₂, hm₂⟩, ?_⟩
        · rw [← Category.assoc, hfq]
        · rintro f' ⟨hs, m', hm'⟩
          refine funiq f' ⟨?_, m', hm'⟩
          obtain ⟨mcomp⟩ := objMap_comp p D R b N T Y M.X (c ≫ M.s) (q ≫ M.s) M.s o u M.univ f' q m' mu
          exact cuniq (f' ≫ q) ⟨by rw [Category.assoc, ← hs], ⟨mcomp⟩⟩ }
  exact ⟨E, q, act, rfl, ⟨mu⟩, hgal⟩
