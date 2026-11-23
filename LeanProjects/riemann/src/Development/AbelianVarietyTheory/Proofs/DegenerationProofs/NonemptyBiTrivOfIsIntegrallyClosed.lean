import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.BiextTriv

theorem nonempty_biTriv_of_isIntegrallyClosed (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (L : RigLB G) (c : CubicalStr G L)
    (i : splitTorus _ X ⟶ G) [IsMonHom i] : Nonempty (BiTriv c i) := by
  have : IsIntegral G.left := isIntegral_of_smooth_of_geometricallyConnected G.hom
  have : IsIntegral (G ⊗ G).left := by
    have : Smooth (fst G G).left := inferInstanceAs (Smooth (pullback.fst G.hom G.hom))
    have : GeometricallyConnected (fst G G).left :=
      inferInstanceAs (GeometricallyConnected (pullback.fst G.hom G.hom))
    exact isIntegral_of_smooth_of_geometricallyConnected (fst G G).left
  have : IsIntegral (splitTorus (Spec (CommRingCat.of A)) X ⊗ G).left := by
    have : Smooth (snd (splitTorus (Spec (CommRingCat.of A)) X) G).left :=
      inferInstanceAs (Smooth (pullback.snd (splitTorus (Spec (CommRingCat.of A)) X).hom G.hom))
    have : GeometricallyIntegral (snd (splitTorus (Spec (CommRingCat.of A)) X) G).left :=
      inferInstanceAs (GeometricallyIntegral (pullback.snd (splitTorus (Spec (CommRingCat.of A)) X).hom G.hom))
    exact isIntegral_of_geometricallyIntegral (snd (splitTorus (Spec (CommRingCat.of A)) X) G).left
  obtain ⟨s, hs, hn⟩ := exists_normalised_gen (φ := lamφ i) (ε := Oε) (fun U hU => by
      have : IsAffine U.1.toScheme := U.2
      have : IsIntegral U.1.toScheme := isIntegral_of_isOpenImmersion U.1.ι
      have h := (HasRingHomProperty.appTop (P := @Smooth) (U.1.ι ≫ G.hom) inferInstance)
      algebraize [(U.1.ι ≫ G.hom).appTop.hom]
      have : IsIntegrallyClosed Γ(Spec (CommRingCat.of A), ⊤) :=
        IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
      exact isIntegrallyClosed_of_smooth Γ(Spec (CommRingCat.of A), ⊤) _) L.isLB fun V _ h => by
    refine (prod_lam i 1 (𝟙 G) V h).trans ?_
    simp [lamForm]
  have R := (rep_val hs).mul (rep_lam i hs (fst (splitTorus _ X) G) 1).inv
  obtain ⟨s', hs', hv⟩ := exists_gen_of_rep L.isLB (lamφ i) Oε R fun V _ h => by simp [lamForm]
  have hv' : ∀ (Z : Over (Spec (CommRingCat.of A))) (t : Z ⟶ splitTorus _ X) (x : Z ⟶ G) z J, Good L.L z J →
      val s' (lift t x).left z J = val s (lift t x).left z J * (val s (lift t (1 : Z ⟶ G)).left z J)⁻¹ :=
    fun Z t x z J hJ => by rw [hv _ _ z J hJ, ← Over.comp_left, comp_lift, lift_fst, MonObj.comp_one]
  refine nonempty_biTriv c i hs' (fun Z y z J hJ => (hv' Z 1 y z J hJ).trans ?_) fun Z t z J hJ => ?_
  · exact mul_inv_eq_one.2 ((hn Z y z J hJ).trans (hn Z 1 z J hJ).symm)
  · rw [hv' Z t 1 z J hJ, mul_inv_cancel]

theorem nonempty_biTriv_normal : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (L : RigLB G) (c : CubicalStr G L) (i : splitTorus _ X ⟶ G), IsMonHom i → Nonempty (BiTriv c i) :=
  fun _ _ A _ _ _ _ X _ _ _ G _ _ _ _ L c i _ => nonempty_biTriv_of_isIntegrallyClosed A X G L c i

end GlobalTheory.BiextTriv
