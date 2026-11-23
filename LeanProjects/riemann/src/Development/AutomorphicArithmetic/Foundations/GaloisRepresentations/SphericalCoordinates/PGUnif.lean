import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactOfQProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationOfMarkedPeriodsFamilyStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

theorem gUnif_of : ModelEx → GenCmp → GenPts → BaseC → GFine → GUnif := by
  intro hM hC hP hB hF p _ D ha hm t₀ ht ρ hρ gb hgb N hN hNp X
  obtain ⟨b, hbρ, hbt, hbT⟩ := hB p D ha hm t₀ ht ρ hρ gb hgb
  obtain ⟨M⟩ := hM p D ℂ b N hN hNp
  obtain ⟨j, hjo, hjc, hjs, hjG⟩ := hC p D ℂ b ℂ (RingHom.id ℂ) gb hbρ hbt N hN hNp M X
  have hpts := hP p D ℂ b (RingHom.id ℂ) gb hbρ hbt N hN hNp M X j hjo hjc hjs hjG
  obtain ⟨h, hL, -⟩ := model_uniformised p D ℂ b N (RingHom.id ℂ) ρ M hN hNp hbT
  have hfine := T.complexPoints_classify_markedPeriods p D ℂ b N (RingHom.id ℂ) ρ M h hL (by omega) hNp hbT
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by
    simp [spMap]
  have hsq : (j ≫ pullback.fst M.s (spMap (RingHom.id ℂ))) ≫ M.s = X.s := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hjs, hid, Category.comp_id]
  obtain ⟨hX, hL', hXf⟩ := hF p D b gb N M X ρ h hL _ hsq hjG hpts hfine
  haveI := hjo
  haveI := hjc
  have hsm : SmoothOfRelativeDimension (D.n - 1) X.s := by
    have h1 : SmoothOfRelativeDimension (D.a * (D.n - 1)) M.s := M.smooth
    rw [ha, Nat.one_mul] at h1
    haveI : SmoothOfRelativeDimension (D.n - 1) (pullback.snd M.s (spMap (RingHom.id ℂ))) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange (D.n - 1)).of_isPullback
        (IsPullback.of_hasPullback _ _) h1
    have h3 : SmoothOfRelativeDimension (0 + (D.n - 1))
        (j ≫ pullback.snd M.s (spMap (RingHom.id ℂ))) := inferInstance
    rw [Nat.zero_add, hjs] at h3
    exact h3
  have hqc : QuasiCompact X.s := by
    haveI : QuasiCompact M.s := quasiCompact_of_qProj M.qproj
    rw [← hjs]
    infer_instance
  have hsep : IsSeparated X.s := by
    haveI : IsSeparated M.s := by
      obtain ⟨K, i, hi, -, hiK⟩ := M.qproj
      haveI := hi
      haveI := isProper_str ℂ K
      rw [← hiK]
      infer_instance
    rw [← hjs]
    infer_instance
  refine ⟨hsm, hqc, hsep, hX, hL', hXf, ?_⟩
  refine T.complexUniformisation_of_markedPeriods_family _ _ _ ρ _ (gfam X.univ hX hL') N (D.Cls N) (D.n - 1) hN ?_ hsm hqc
    (fun D' t ht => Datum.Cls.fullMark D N (by omega) hNp D' t ht) hXf
  intro a
  change X.univ.eta a ^ N = 1
  rw [← GObj.eta_nsmul, GObj.eta_ker]

end UpperTheory.Gal.W2
