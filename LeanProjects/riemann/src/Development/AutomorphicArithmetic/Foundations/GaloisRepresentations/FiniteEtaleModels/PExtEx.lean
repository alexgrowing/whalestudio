import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BaseOnto
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFinite

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.extEx_holds :
    MIn → PowProj → ExtEx := by
  intro hM hPP p _ D G hSc E _ _ gb w q _ r 𝔴 𝔫 S N₁ 𝔟 hL
  obtain ⟨h3, hcq, hcp, hsup, hpow⟩ := hL
  obtain ⟨M⟩ := hM.ex q _ (Ow w) S.b N₁ h3 hcq
  have het : IsEtIdeal S.b 𝔟 :=
    (hM.placeOf q _ (Ow w) S.b r 𝔴 S.atq.max S.std.pmem S.std.a1 S.std.ule S.std.tw 𝔟 hsup).2 hpow
  obtain ⟨Y, π, ρ, hov, ⟨m⟩, hG⟩ := hM.finModel q _ (Ow w) S.b N₁ h3 hcq 𝔟 1 het M
  have hfin : IsFinite π := hG.fin
  have het' : Etale π := hG.etale
  have hMp : IsProjOver M.s := hM.proj q _ (Ow w) S.b N₁ h3 hcq hSc.cpt M
  have hYp : IsProjOver Y.s := by
    rw [← hov]
    exact GlobalTheory.isProjOver_comp_of_finite (Ow w) M.X Y.X π M.s hfin hMp
  have hYs : ∃ d, SmoothOfRelativeDimension d Y.s := by
    have h0 := het'
    rw [Etale.iff_smoothOfRelativeDimension_zero] at h0
    have key : ∀ n, SmoothOfRelativeDimension n M.s → SmoothOfRelativeDimension (0 + n) (π ≫ M.s) :=
      fun n hn => inferInstance
    rw [← hov]
    exact ⟨_, key _ M.smooth⟩
  refine ⟨⟨⟨h3, hcq, hcp, hsup, hpow⟩, M, Y, π, hov, m, hfin, het', fun k => ?_, fun k => ?_⟩⟩
  · exact (hPP q _ (Ow w) S.b N₁ h3 hcq Y.X Y.s Y.univ k).1 hYp
  · obtain ⟨d, hd⟩ := hYs
    exact (hPP q _ (Ow w) S.b N₁ h3 hcq Y.X Y.s Y.univ k).2 d hd
