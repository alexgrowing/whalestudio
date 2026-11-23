import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjectiveStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.AmpleSubring

theorem relAmple_subring : ∀ (S : Type) [CommRing S] [IsLocalRing S] (R₀ : Subring S) [IsNoetherianRing R₀] (P : Out.PolAV (Sp S)) (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : P.A.left ⟶ A₀.left) (L₀ : LB A₀.left), IsAbelianScheme A₀ → IsProjOver A₀.hom → L₀.IsLB → IsGrpPullback P.A A₀ (spMap R₀.subtype) φ → LBIso P.L (L₀.pull φ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (π : A₁.left ⟶ A₀.left), IsGrpPullback A₁ A₀ (spMap (Subring.inclusion h)) π → Out.RelAmple A₁ (L₀.pull π) := by
  intro S _ _ R₀ _ P A₀ _ φ L₀ hA₀ hproj hL₀ hφ e
  have := hA₀.proper
  have := hA₀.smooth
  let x : R₀ →+* IsLocalRing.ResidueField S := (IsLocalRing.residue S).comp R₀.subtype
  let p : Ideal R₀ := RingHom.ker x
  have : p.IsPrime := RingHom.ker_isPrime x
  let g := algebraMap R₀ p.ResidueField
  let i : p.ResidueField →+* IsLocalRing.ResidueField S :=
    Ideal.ResidueField.lift p x le_rfl fun a ha => IsUnit.mk0 _ ha
  have hi : i.comp g = x := RingHom.ext fun a => Ideal.ResidueField.lift_algebraMap p x le_rfl
    (fun a ha => IsUnit.mk0 _ ha) a
  have hu : spMap (IsLocalRing.residue S) ≫ spMap R₀.subtype = spMap i ≫ spMap g := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hi]
  have h₂ := IsPullback.of_hasPullback A₀.hom (spMap i ≫ spMap g)
  obtain ⟨r, hr, hA⟩ := GlobalTheory.T.relAmple_near_fibre_flat_projective R₀ A₀ L₀ inferInstance
    ((ProjSpace.isProjBy_iff_isProjOver _).2 hproj) hL₀ _ g (FibreAmple.residueField_fraction p)
    (FibreAmple.relAmple_of_fieldExtension hL₀ i (IsPullback.of_hasPullback A₀.hom (spMap g)) h₂
      (LB.isLB_pull hL₀ _) (GlobalTheory.lbIso_refl (LB.isLB_pull hL₀ _))
      (FibreAmple.relAmple_of_factor hL₀ hφ.1 h₂ _ hu P.isLB e P.ample))
  have hx : x r ≠ 0 := fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)
  obtain ⟨v, hv⟩ : IsUnit (r : S) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hx
  refine ⟨{v⁻¹.val}, fun R₁ h hF A₁ _ π hπ => ?_⟩
  have hu₁ : IsUnit (Subring.inclusion h r) :=
    IsUnit.of_mul_eq_one (⟨v⁻¹.val, hF (by simp)⟩ : R₁) (Subtype.ext (by
      change (r : S) * v⁻¹.val = 1
      rw [← hv, Units.mul_inv]))
  let D : (Spec (CommRingCat.of R₀)).Opens := PrimeSpectrum.basicOpen r
  have hrange : Set.range (spMap (Subring.inclusion h)) ⊆ Set.range D.ι := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨_, fun hm => z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu₁)⟩, rfl⟩
  exact FibreAmple.relAmple_of_factor hL₀ (IsPullback.of_hasPullback A₀.hom D.ι) hπ.1
    (IsOpenImmersion.lift D.ι _ hrange) (IsOpenImmersion.lift_fac _ _ _) (LB.isLB_pull hL₀ _)
    (GlobalTheory.lbIso_refl (LB.isLB_pull hL₀ _)) hA

end GlobalTheory.AmpleSubring
