import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixRepBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommMonObjOfGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndPullOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleAtBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBaseChangeStableSectionBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedPullbackHomSchemeOfSectionBasesStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.HomFixLocal

theorem exists_local_homFixRep : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∀ p : Sp Rg, ∃ U : (Sp Rg).Opens, p ∈ U ∧ ∃ (AU : Over (U).toScheme) (_ : GrpObj AU) (BU : Over (U).toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A (U).ι φA ∧ IsGrpPullback BU B (U).ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro Rg _ _ A B _ _ _ _ L M hA hB hL hM rL rM aL aM p
  obtain ⟨k, hk, hva⟩ := GlobalTheory.RelAmpleFixed.veryAmpleAt_baseChange Rg B M hB hM aM
  obtain ⟨f₁, hp₁, hb₁⟩ := GlobalTheory.T.exists_basicOpen_baseChangeStable_sectionBasis Rg A L hA hL rL aL k hk p
  obtain ⟨f₂, hp₂, hb₂⟩ := GlobalTheory.T.exists_basicOpen_baseChangeStable_sectionBasis Rg B M hB hM rM aM k hk p
  have le₁ : PrimeSpectrum.basicOpen (f₁ * f₂) ≤ PrimeSpectrum.basicOpen f₁ := by
    rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_left
  have le₂ : PrimeSpectrum.basicOpen (f₁ * f₂) ≤ PrimeSpectrum.basicOpen f₂ := by
    rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_right
  have hp : p ∈ PrimeSpectrum.basicOpen (f₁ * f₂) := by
    rw [PrimeSpectrum.basicOpen_mul]; exact ⟨hp₁, hp₂⟩
  refine ⟨PrimeSpectrum.basicOpen (f₁ * f₂), hp, GlobalTheory.HomFixTransport.homFixRep_basicOpen Rg A B L M (f₁ * f₂) hL hM ?_ _ rfl⟩
  intro Af Bf _ _ φA φB hpA hpB
  haveI := GlobalTheory.isCommMonObj_of_grpPullback _ _ A Af _ φA hpA
  haveI := GlobalTheory.isCommMonObj_of_grpPullback _ _ B Bf _ φB hpB
  obtain ⟨hA', hL', rL', aL'⟩ := GlobalTheory.GrpPullbackPol.isAbelianScheme_and_pull_of_isGrpPullback _ _ _ A Af φA L hpA hA hL rL aL
  obtain ⟨hB', hM', rM', -⟩ := GlobalTheory.GrpPullbackPol.isAbelianScheme_and_pull_of_isGrpPullback _ _ _ B Bf φB M hpB hB hM rM aM
  exact GlobalTheory.T.exists_fixedPullbackHomScheme_of_sectionBases (Localization.Away (f₁ * f₂)) Af Bf (L.pull φA) (M.pull φB) k hA' hB' hL' hM' rL' rM' aL' hk
    (hva _ _ Bf φB hpB) (hb₁ _ le₁ Af φA hpA) (hb₂ _ le₂ Bf φB hpB)

end GlobalTheory.HomFixLocal
