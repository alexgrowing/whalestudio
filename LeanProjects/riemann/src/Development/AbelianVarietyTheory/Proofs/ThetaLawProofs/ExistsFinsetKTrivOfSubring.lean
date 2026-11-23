import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasicOpenKTrivOfFibre

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory

open scoped CategoryTheory.Obj in

theorem exists_finset_kTriv_of_subring :
    ∀ (S : Type) [CommRing S] [IsLocalRing S] (R₀ : Subring S) [IsNoetherianRing R₀] (P : Out.PolAV (Sp S)) (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : P.A.left ⟶ A₀.left) (L₀ : LB A₀.left), IsAbelianScheme A₀ → L₀.IsLB → Out.RelAmple A₀ L₀ → IsGrpPullback P.A A₀ (spMap R₀.subtype) φ → LBIso P.L (L₀.pull φ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (π : A₁.left ⟶ A₀.left), IsGrpPullback A₁ A₀ (spMap (Subring.inclusion h)) π → Out.KTriv A₁ (L₀.pull π) := by
  intro S _ _ R₀ _ P A₀ _ φ L₀ hA hL hamp hφ e
  let r : S →+* IsLocalRing.ResidueField S := IsLocalRing.residue S
  have h₁ := isGrpPullback_pullback P.A (spMap r)
  have hc : spMap r ≫ spMap R₀.subtype = spMap (r.comp R₀.subtype) := by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have h₂ := h₁.comp hφ
  rw [hc] at h₂
  obtain ⟨w, hw⟩ : LBIso (L₀.pull (pullback.fst P.A.hom (spMap r) ≫ φ))
      (P.L.pull (pullback.fst P.A.hom (spMap r))) :=
    LBIso.symm (LBIso.chartPull (chartPullPull P.L _)
      (chartPullSame L₀ (fun _ : PUnit => pullback.fst P.A.hom (spMap r) ≫ φ) (fun _ => φ) (fun _ => 1) _
        fun _ => rfl) e)
  have hK := kTriv_pull h₁ P.isLB (pull_isLB hL _) ((isGen_iff w).1 hw) P.ktriv
  obtain ⟨f, hf, H⟩ := GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit R₀ A₀ L₀ _ (r.comp R₀.subtype) _ _ hA hL hamp h₂ hK
  have hu : IsUnit (f : S) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hf
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  refine ⟨{g}, fun R₁ h hF A₁ _ π hπ => H R₁ (Subring.inclusion h) A₁ π ?_ hπ⟩
  have hg₁ : g ∈ R₁ := hF (by simp)
  exact IsUnit.of_mul_eq_one (⟨g, hg₁⟩ : R₁) (Subtype.ext hg)

end GlobalTheory
