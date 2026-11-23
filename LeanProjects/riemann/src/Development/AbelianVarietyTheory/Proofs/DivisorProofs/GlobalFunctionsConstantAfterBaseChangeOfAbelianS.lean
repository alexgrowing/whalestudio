import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.OneTmulNeZeroOfDomain
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsNoetherianModelOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

open Opposite TopologicalSpace

theorem uConst_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → UConst A.hom := by
  intro R _ A _ hA R' _ _ X' s' φ hpb
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hsm : Smooth s' := MorphismProperty.of_isPullback hpb ‹_›
  have hpr : IsProper s' := MorphismProperty.of_isPullback hpb ‹_›
  have hgc : GeometricallyConnected s' := MorphismProperty.of_isPullback hpb ‹_›
  haveI : GeometricallyIntegral s' :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected X' _ s' hsm hgc
  have hiso : IsIso s'.appTop := GlobalTheory.GlobalFunctions.isIso_app GlobalTheory.FlatFibreInjective.injective_baseChange
    GlobalTheory.exists_noetherian_model_of_smooth s' ⊤
  have hbij := ConcreteCategory.bijective_of_isIso s'.appTop
  intro g hg
  have hc : ∀ (U V : X'.affineOpens) (h : V.1 ≤ U.1),
      X'.presheaf.map (homOfLE h).op (g (op U)) = g (op V) := by
    intro U V h
    have e := congrFun (congrFun (congrFun hg (op U)) (op V)) (homOfLE h).op
    exact (sub_eq_zero.1 e).symm
  obtain ⟨t, ht, htu⟩ := X'.sheaf.existsUnique_gluing' (fun U : X'.affineOpens ↦ U.1) ⊤
    (fun _ ↦ homOfLE le_top) (iSup_affineOpens_eq_top X').ge (fun U ↦ g (op U)) (by
      intro U V
      refine X'.sheaf.eq_of_locally_eq' (fun W : {W : X'.affineOpens // W.1 ≤ U.1 ⊓ V.1} ↦ W.1.1)
        (U.1 ⊓ V.1) (fun W ↦ homOfLE W.2) ?_ _ _ fun W ↦ ?_
      · intro x hx
        obtain ⟨W, hW, hxW, hWUV⟩ := Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens hx
        exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWUV⟩, hxW⟩
      · dsimp only
        have e : ∀ {a b c : Opens X'} (f : b ⟶ a) (f' : c ⟶ b) (x : Γ(X', a)),
            X'.presheaf.map f'.op (X'.presheaf.map f.op x) = X'.presheaf.map (f' ≫ f).op x := by
          intros; simp
        refine (e _ _ _).trans ((hc U W.1 (W.2.trans inf_le_left)).trans
          ((hc V W.1 (W.2.trans inf_le_right)).symm.trans (e _ _ _).symm)))

  have hres : ∀ (r : R') (U : X'.affineOpens),
      X'.presheaf.map (homOfLE le_top).op (s'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv r)) =
        algebraMap R' (Sec s' U.1) r := by
    intro r U
    rfl
  have hres' : ∀ (x : Γ(Sp R', ⊤)) (U : X'.affineOpens),
      X'.presheaf.map (homOfLE le_top).op (s'.appTop x) =
        algebraMap R' (Sec s' U.1) ((Scheme.ΓSpecIso (CommRingCat.of R')).hom x) := by
    intro x U
    have := hres ((Scheme.ΓSpecIso (CommRingCat.of R')).hom x) U
    rw [Iso.hom_inv_id_apply] at this
    exact this
  obtain ⟨r₀, hr₀⟩ := hbij.2 t
  subst hr₀
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R')).hom r₀, ?_, ?_⟩
  · intro U
    exact (ht U.unop).symm.trans (hres' r₀ U.unop)
  · intro r hr
    have h1 : s'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv r) = s'.appTop r₀ := by
      apply htu
      intro U
      exact (hres r U).trans (hr (op U)).symm
    have h2 := hbij.1 h1
    rw [← h2, Iso.inv_hom_id_apply]

end GlobalTheory.AbCoh
