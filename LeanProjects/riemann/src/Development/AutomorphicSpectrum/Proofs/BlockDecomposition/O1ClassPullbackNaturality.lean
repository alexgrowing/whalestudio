import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoheightEqOneOfDimClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLineBundleSectionsGenerateIdealSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DimOfIsArithVar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MixZ

def chartPullPullO {R : Type} [CommRing R] {N : ℕ} {S T : Scheme.{0}} (r : T ⟶ S) (φ : S ⟶ PSpace R N) :
    ChartPull (pullO (r ≫ φ) 1) (pullO φ 1) r where
  idx i := i
  le _ _ h := h
  g y i j hi hj := by
    have hle : (pullO (r ≫ φ) 1).U i ⊓ (pullO (r ≫ φ) 1).U j ≤
        r ⁻¹ᵁ ((pullO φ 1).U i ⊓ (pullO φ 1).U j) := fun _ h => h
    have hm : r y ∈ (pullO φ 1).U i ⊓ (pullO φ 1).U j := ⟨hi, hj⟩
    have ev : (((pullO φ 1).g i j : Γ(S, (pullO φ 1).U i ⊓ (pullO φ 1).U j)ˣ) :
        Γ(S, (pullO φ 1).U i ⊓ (pullO φ 1).U j)) = pullRatio φ _ i inf_le_left j :=
      (Units.val_pow_eq_pow_val _ _).trans (pow_one _)
    have ev' : (((pullO (r ≫ φ) 1).g i j : Γ(T, (pullO (r ≫ φ) 1).U i ⊓ (pullO (r ≫ φ) 1).U j)ˣ) :
        Γ(T, (pullO (r ≫ φ) 1).U i ⊓ (pullO (r ≫ φ) 1).U j)) = pullRatio (r ≫ φ) _ i inf_le_left j :=
      (Units.val_pow_eq_pow_val _ _).trans (pow_one _)
    have e : (pullO (r ≫ φ) 1).g i j = res hle (pullU r _ ((pullO φ 1).g i j)) := by
      apply Units.ext
      refine ev'.trans (Eq.trans ?_ (congrArg (r.appLE _ _ hle).hom ev).symm)
      exact (appLE_pullRatio (hi := inf_le_left) r hle).symm
    rw [e, gm_res (𝟙 T) y hle ⟨hi, hj⟩, gm_pull (𝟙 T) r y _ hm, Category.id_comp]

theorem cls_pullO_comp {R : Type} [CommRing R] {N : ℕ} {S T : Scheme.{0}} (r : T ⟶ S) (φ : S ⟶ PSpace R N) :
    cls (pullO (r ≫ φ) 1) (isLB_pullO _ 1) = CechPic.pull r (cls (pullO φ 1) (isLB_pullO _ 1)) := by
  rw [← cls_pull (isLB_pullO φ 1) r (pull_isLB (isLB_pullO φ 1) r)]
  exact (cls_eq_iff _ _).2 (LBIso.chartPull (chartPullPullO r φ)
    (chartPullPull (pullO φ 1) r) (PolBaseChange.lbIso_refl (isLB_pullO φ 1)))

end GlobalTheory.CompanionTheory.MixZ
