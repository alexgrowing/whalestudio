import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupConn

theorem connectedSpace_of_section {X S : Scheme.{0}} (f : X ⟶ S) [GeometricallyConnected f]
    [ConnectedSpace S] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) : ConnectedSpace X := by

  have hsec : ∀ y : S, f (s y) = y := fun y => by
    simpa using congrArg (fun g : S ⟶ S => g y) hs
  obtain ⟨y₀⟩ := (inferInstance : Nonempty S)
  refine connectedSpace_iff_connectedComponent.mpr ⟨s y₀, Set.eq_univ_iff_forall.mpr fun x => ?_⟩
  have hbase : s (f x) ∈ connectedComponent (s y₀) :=
    (isPreconnected_range s.continuous).subset_connectedComponent ⟨y₀, rfl⟩ ⟨f x, rfl⟩
  have hfib : x ∈ connectedComponent (s (f x)) :=
    (f.isConnected_preimage_singleton (f x)).isPreconnected.subset_connectedComponent
      (show f (s (f x)) = f x from hsec (f x)) rfl
  rw [connectedComponent_eq hbase]
  exact hfib

theorem connectedSpace_tensor {S : Scheme.{0}} (G : Over S) [GrpObj G] [GeometricallyConnected G.hom]
    (Y : Over S) [ConnectedSpace Y.left] : ConnectedSpace (G ⊗ Y).left := by

  have : GeometricallyConnected (snd G Y).left :=
    show GeometricallyConnected (pullback.snd G.hom Y.hom) from inferInstance
  have hsec : (lift (toUnit Y ≫ η[G]) (𝟙 Y)).left ≫ (snd G Y).left = 𝟙 Y.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  exact connectedSpace_of_section (snd G Y).left _ hsec

theorem connectedSpace_group : ∀ (S : Scheme.{0}) [ConnectedSpace S] (G : Over S) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom], ConnectedSpace G.left ∧ ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (Y : Over S), ConnectedSpace Y.left → ConnectedSpace (splitTorus S X ⊗ Y).left ∧ ConnectedSpace (G ⊗ Y).left := by
  intro S _ G _ _ _
  refine ⟨connectedSpace_of_section (S := S) (X := G.left) G.hom η[G].left (Over.w _),
    fun X _ _ Y _ => ⟨?_, connectedSpace_tensor G Y⟩⟩

  have : UniqueSums X :=
    UniqueSums.of_injective_addHom (Module.Free.chooseBasis ℤ X).repr.toAddEquiv.toAddHom
      (Module.Free.chooseBasis ℤ X).repr.injective inferInstance
  exact connectedSpace_tensor (splitTorus S X) Y

end GlobalTheory.GroupConn
