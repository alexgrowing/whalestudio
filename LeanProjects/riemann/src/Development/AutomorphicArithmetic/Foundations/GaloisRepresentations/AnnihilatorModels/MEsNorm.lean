import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.FrobKill
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelValueIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPotentialBlockDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePartialBlockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFlagBundleMetricLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedNormalModelGenericCorrespondence
import Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteFlatCoverModelIntegral

open private isDomain_of_isReduced_of_isIntegrallyClosed from Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteFlatCoverModelIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem UpperTheory.Gal.crystallineComparison.Mod.esNorm_of (hG : UpperTheory.Gal.crystallineComparison.Mod.EsGen) : UpperTheory.Gal.crystallineComparison.Mod.EsNorm := by
  intro p _ D R _ _ _ _ b N h3 hcop hp r w j c hw hu hj hc hm M
  obtain ⟨Y₀, s₀, t₀, gs, gt, o₀, o₀', ms₀, mt₀, ψ₀, hst₀, hgs, hgt, hfgs, hegs, hfgt, hegt, hiso₀, htj₀, huniv₀⟩ :=
    hG p D R b N h3 hcop hp r w j c hw hu hj hc hm M
  obtain ⟨Y, s, i, hio, hid, hi, hfs, hnorm, hflat, hnoeth, hext⟩ :=
    NormCover.exists_finite_normal_model p D R b N hp M Y₀ s₀ gs hfgs hegs hgs
  obtain ⟨t, hit, ht, hft⟩ := GlobalTheory.ExtT.exists_finite_extension p D R b N h3 hcop hp r w j c hw hu hj hc hm M
    Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst₀ hgs hgt hfgs hegs hfgt hegt hiso₀ htj₀ Y s i hio hid hi hfs hnorm hflat
    hnoeth hext
  have hred : AlgebraicGeometry.IsReduced Y :=
    isReduced_normalModel_of_generic p D R b N hp M Y₀ s₀ gs hgs hegs Y s i hio hi hflat hext
  have hdom : ∀ y : Y, IsDomain (Y.presheaf.stalk y) := fun y => by
    haveI := hnorm y
    exact isDomain_of_isReduced_of_isIntegrallyClosed _
  obtain ⟨o, ⟨ms⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X Y M.s s M.univ
  have hpt := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X Y M.s t M.univ
  rw [ht] at hpt
  obtain ⟨o', ⟨mt⟩⟩ := hpt
  subst hi
  subst hit
  obtain ⟨m, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ ms₀ ms
  obtain ⟨m', -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ mt₀ mt
  obtain ⟨ψ, hiso, hcomm⟩ := PIsogExt.exists_isPIsog_extend p D R b N h3 hcop j c hc Y₀ Y i _ _ hio hid hnoeth
    hnorm hdom o o' o₀ o₀' m m' ψ₀ hiso₀
  refine ⟨Y, s, t, o, o', ms, mt, ψ, ht.symm, hfs, hft, hnorm, hflat, hiso, ?_, ?_⟩
  · exact isTj_of_objMap_factor p D R b N r w j Y₀ Y i _ _ o o' o₀ o₀' m m' ψ₀ ψ hcomm hext htj₀
  · exact existsUnique_of_openImmersion p D R b N h3 hcop r w j c M Y₀ Y i (i ≫ s) s _ _ o o' o₀ o₀' m m'
      ψ₀ ψ hio rfl hcomm hext huniv₀
