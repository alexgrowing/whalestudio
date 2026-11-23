import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMonHomIdPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullback
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (KS Lv Sc Integ IsTrans)

namespace UpperTheory.Gal.FixZ

private theorem powMap_scal {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (d k : ℕ) (Φ : A.left ⟶ A.left)
    (hw : Φ ≫ A.hom = A.hom ≫ 𝟙 S) (h : Φ = ((𝟙 A) ^ d).left) :
    GlobalTheory.KS.powMap (𝟙 S) Φ hw k = (Limits.Pi.map (fun _ : Fin k => (𝟙 A) ^ d)).left := by
  apply GlobalTheory.KS.PowPB.pow_left_hom_ext
  · rw [GlobalTheory.KS.PowPB.powMap_w, Over.w, Category.comp_id]
  · intro i
    rw [GlobalTheory.KS.PowPB.powMap_pr, h, ← Over.comp_left, ← Over.comp_left]
    congr 1
    unfold KS.pr
    simp

end UpperTheory.Gal.FixZ

theorem UpperTheory.Gal.FixZ.trScal_of :
    UpperTheory.Gal.G3.WitUniq → UpperTheory.Gal.G3.IsogFEt → UpperTheory.Gal.FixZ.WitScal → UpperTheory.Gal.FixZ.PowFEt → UpperTheory.Gal.FixZ.TrScal := by
  intro hWU hIso hWS hPow p _ D G L gb k T N d z hd hdp hsc a b
  obtain ⟨π, o, ψ, φ, hw, hπ, htr, heq⟩ := T.tr_eq N N z a b
  have hI : Integ L z := (T.Δ_eq z).1 a
  have hA : UpperTheory.Gal.G3.AdmK L N.1 N.1 z := by
    intro u hu
    have hb := b u (by rw [T.K_eq]; exact hu)
    rwa [T.K_eq] at hb
  obtain ⟨rfl, hΦ⟩ := hWU p D G L ℂ gb N N (T.M N) (T.M N) z hI hA π (Over.Hom.left ψ ≫ φ.φ) (𝟙 _)
    (Over.Hom.left (𝟙 (T.M N).univ.A ^ d)) ⟨hπ, o, ψ, φ, htr, rfl⟩ (hWS p D G L gb N (T.M N) d z hd hdp hsc)
  have hpm := GlobalTheory.DrinLev.HT.MulModel.isMonHom_id_pow (T.M N).univ.A d
  have hS := powMap_scal (T.M N).univ.A d k _ hw hΦ
  rw [hS] at heq
  have hfe : IsFinite (Over.Hom.left (𝟙 (T.M N).univ.A ^ d)) ∧ Etale (Over.Hom.left (𝟙 (T.M N).univ.A ^ d)) ∧
      Surjective (Over.Hom.left (𝟙 (T.M N).univ.A ^ d)) := by
    refine hIso ℂ _ (T.M N).s _ _ (T.M N).univ.ab (T.M N).univ.ab (𝟙 _ ^ d) (𝟙 _ ^ d) (d * d)
      (Nat.mul_pos hd hd) hpm hpm ?_ ?_
    · rw [MonObj.comp_pow, Category.comp_id, ← pow_mul]
    · rw [MonObj.comp_pow, Category.comp_id, ← pow_mul]
  obtain ⟨hf1, hf2, -⟩ := hPow _ (T.M N).univ.A k (fun _ => 𝟙 _ ^ d) (fun _ => hfe)
    (Limits.Pi.map (fun _ : Fin k => 𝟙 (T.M N).univ.A ^ d)) (fun i => by unfold KS.pr; simp)
  have htr' : T.X.tr (T.lev N) (T.lev N) z a b =
      (T.e N).hom ≫ Over.Hom.left (Limits.Pi.map (fun _ : Fin k => 𝟙 (T.M N).univ.A ^ d)) ≫ (T.e N).inv := by
    rw [← Category.assoc, ← heq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [htr']
  constructor
  · infer_instance
  · infer_instance
