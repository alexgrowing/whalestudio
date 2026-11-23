import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.SecInjG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTjExF

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

open private et_of from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTjExF

theorem UpperTheory.Gal.FiniteEtaleModels.tjExG_of :
    UpperTheory.Gal.crystallineComparison.Mod.EsNorm → UpperTheory.Gal.crystallineComparison.Mod.EsGen → UpperTheory.Gal.crystallineComparison.Mod.ObjTri → UpperTheory.Gal.crystallineComparison.Mod.PullIsog → UpperTheory.Gal.crystallineComparison.Mod.PullKer → TjExG := by
  intro hN hG hT hPI hPK p _ D R _ _ _ _ b N h3 hcp hpm hm1 r w j e hw hle hj he M
  obtain ⟨Y, s, t, o, o', ms, mt, ψ, hst, hfs, -, -, -, hiso, htj, hu⟩ :=
    hN p D R b N h3 hcp hpm r w j (p ^ e) hw hle hj ⟨e, rfl, he⟩ hm1 M
  obtain ⟨Y₀, s₀, t₀, gs, gt, o₀, o₀', ms₀, mt₀, ψ₀, -, hgs, -, -, hgse, -, -, hiso0, htj0, hu0⟩ :=
    hG p D R b N h3 hcp hpm r w j (p ^ e) hw hle hj ⟨e, rfl, he⟩ hm1 M
  exact ⟨⟨Y, s, t, hst, o, o', ms, mt, ψ, hfs,
    et_of hT hPI hPK h3 hcp ms hiso htj hu gs hgs hgse ms₀ hiso0 htj0 hu0, hiso, htj, hu⟩⟩
