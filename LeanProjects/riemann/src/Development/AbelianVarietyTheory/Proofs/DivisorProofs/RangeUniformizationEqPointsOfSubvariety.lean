import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapCompSpMap
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
open GlobalTheory.HorComp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HorComp

section

open Limits

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {Y : Scheme.{0}} {q : Y ⟶ Sp Oz}

theorem ptOf_up (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) (y : CxPts q (σ.comp β)) :
    ptOf Z (up j hj σ y) = toGenCx j hj σ
      ((pullback.lift y.1 (𝟙 _) (y.2.trans (Category.id_comp _).symm) : Sp ℂ ⟶ cxFib β q σ)
        (IsLocalRing.closedPoint ℂ)) := by
  have e : (pullback.lift (up j hj σ y).1 (𝟙 _) ((up j hj σ y).2.trans (Category.id_comp _).symm) : Sp ℂ ⟶ genCx Z σ) =
      (pullback.lift y.1 (𝟙 _) (y.2.trans (Category.id_comp _).symm) : Sp ℂ ⟶ cxFib β q σ) ≫ toGenCx j hj σ := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [toGenCx, toGen, up, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · simp only [toGenCx, toGen, up, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc,
          Category.id_comp]
    · refine (pullback.lift_snd _ _ _).trans ?_
      rw [Category.assoc]
      exact ((congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans (pullback.lift_snd _ _ _)).symm
  exact congrArg (fun g : Sp ℂ ⟶ genCx Z σ => g (IsLocalRing.closedPoint ℂ)) e

theorem range_up_eq_ptsOf (j : Y ⟶ Z.X) [IsClosedImmersion j] (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) :
    Set.range (up j hj σ) = ptsOf Z (Set.range (toGenCx j hj σ)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, (ptOf_up j hj σ y).symm⟩
  · rintro ⟨w, hw⟩
    have e : toGenCx j hj σ ≫ pullback.fst _ _ ≫ genι Z = pullback.fst _ _ ≫ j := by
      simp only [toGenCx, toGen, pullback.lift_fst, pullback.lift_fst_assoc]
    have h1 : (x.1 ≫ genι Z) (IsLocalRing.closedPoint ℂ) = j (pullback.fst q (spMap (σ.comp β)) w) := by
      have h2 := congrArg (fun g : cxFib β q σ ⟶ Z.X => g w) e
      simp only [Scheme.Hom.comp_apply] at h2 ⊢
      rw [← h2, hw, fst_ptOf]
      rfl
    have hr : Set.range (x.1 ≫ genι Z) ⊆ Set.range j := by
      rintro _ ⟨p, rfl⟩
      obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      exact ⟨_, h1.symm⟩
    obtain ⟨f, hf⟩ : ∃ f : Sp ℂ ⟶ Y, f ≫ j = x.1 ≫ genι Z := by
      have : Surjective (pullback.snd j (x.1 ≫ genι Z)) := ⟨by
        rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
        exact Set.eq_univ_of_forall fun t => hr ⟨t, rfl⟩⟩
      have : IsIso (pullback.snd j (x.1 ≫ genι Z)) := isIso_of_isClosedImmersion_of_surjective _
      exact ⟨inv (pullback.snd j (x.1 ≫ genι Z)) ≫ pullback.fst j _, by
        rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩
    have hq : f ≫ q = spMap (σ.comp β) := by
      rw [← hj, ← Category.assoc, hf, Category.assoc, pullback.condition, ← Category.assoc, x.2, spMap_comp_spMap]
    refine ⟨⟨f, hq⟩, Subtype.ext ?_⟩
    apply pullback.hom_ext
    · exact (up_ι j hj σ _).trans hf
    · exact (up j hj σ _).2.trans x.2.symm

end

theorem range_up_eq_ptsOf_range_toGenCx_of_isArithVar : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp (𝓞 κ.c.F)) (jm : Y ⟶ s.T.Z.X) [IsClosedImmersion jm] (hq : jm ≫ s.T.Z.s = q) (n : ℕ), IsArithVar q n → Set.range (up jm hq σ) = ptsOf s.T.Z (Set.range (toGenCx jm hq σ)) :=
  fun _ _ _ _ _ _ _ σ _ _ _ jm _ hq _ _ => range_up_eq_ptsOf jm hq σ

end GlobalTheory.HorComp

end
