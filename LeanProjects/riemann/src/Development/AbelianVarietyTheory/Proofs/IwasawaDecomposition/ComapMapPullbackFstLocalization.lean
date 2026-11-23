import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineHomOfIsPullbackSpecMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueComapEqVanishingIdeal
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.LocClosure

set_option backward.isDefEq.respectTransparency false in

theorem comap_map_pullback_fst_localization {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R)
    [IsLocalization M S] (X : Scheme.{0}) (s : X ⟶ Sp R) (K : (pullback s (spMap (algebraMap R S))).IdealSheafData) :
    (K.map (pullback.fst s (spMap (algebraMap R S)))).comap (pullback.fst s (spMap (algebraMap R S))) = K := by
  set π := pullback.fst s (spMap (algebraMap R S))
  have H : IsPullback π (pullback.snd s (spMap (algebraMap R S))) s
      (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of R) (CommRingCat.of S)))) :=
    IsPullback.of_hasPullback _ _
  have : IsAffineHom π := GlobalTheory.QCoh.Qcqs.isAffineHom_of_isPullback_SpecMap H
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun U : X.affineOpens => ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) ?_ fun U => ?_
  · change ⨆ U : X.affineOpens, π ⁻¹ᵁ U.1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · let := (π.app U).hom.toAlgebra
    have hloc := GlobalTheory.QCoh.Qcqs.isLocalization_app (R := CommRingCat.of R) (L := CommRingCat.of S) M H U.2
    have key := IsLocalization.map_comap (M.map (GlobalTheory.QCoh.Qcqs.baseRingHom s U.1).hom) (Γ(pullback s (spMap (algebraMap R S)), π ⁻¹ᵁ U.1))
      (K.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩)
    rw [← key, Ideal.map_le_iff_le_comap]
    intro x hx
    have h5 := GlobalTheory.GaloisDescent.ideal_le_comap_appLE π (le_refl ((K.map π).comap π)) U
      ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ le_rfl (x := x)
      (by rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]; exact hx)
    rw [← Scheme.Hom.app_eq_appLE] at h5
    exact h5

end GlobalTheory.LocClosure
