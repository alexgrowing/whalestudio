import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.RegPull

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem germ_gp (V : Y.Opens) (hY : genericPoint Y ∈ V) (h : gp Y (closedPoint _) ∈ V) :
    Y.presheaf.germ V (gp Y (closedPoint _)) h ≫ Scheme.stalkClosedPointTo (gp Y) =
      Y.presheaf.germ V (genericPoint Y) hY := by
  have hC : ∀ G : Spec (Y.presheaf.stalk (genericPoint Y)) ⟶ Y,
      G = Spec.map (𝟙 _) ≫ Y.fromSpecStalk (genericPoint Y) → ∀ h,
      Y.presheaf.germ V (G (closedPoint _)) h ≫ Scheme.stalkClosedPointTo G =
        Y.presheaf.germ V (genericPoint Y) hY ≫ 𝟙 _ := by
    rintro G rfl h
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (𝟙 _) V h
  have e : gp Y = Spec.map (𝟙 _) ≫ Y.fromSpecStalk (genericPoint Y) := by
    rw [Spec.map_id, Category.id_comp]; rfl
  exact (hC (gp Y) e h).trans (Category.comp_id _)

theorem fnOf_map (π : Y ⟶ X) (θ : X.functionField →+* Y.functionField)
    (e : gp Y ≫ π = spMap θ ≫ gp X) (U : X.Opens) (hX : genericPoint X ∈ U)
    (hY : genericPoint Y ∈ π ⁻¹ᵁ U) (s : Γ(X, U)) :
    θ (fnOf U hX s) = fnOf (π ⁻¹ᵁ U) hY (π.app U s) := by
  have hA : ∀ F : Sp Y.functionField ⟶ X, F = spMap θ ≫ gp X → ∀ hU,
      X.presheaf.germ U (F (closedPoint _)) hU ≫ Scheme.stalkClosedPointTo F =
        X.presheaf.germ U (genericPoint X) hX ≫ CommRingCat.ofHom θ := by
    rintro F rfl hU
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (CommRingCat.ofHom θ) U hU
  have hg : gp Y (closedPoint _) = genericPoint Y := Scheme.fromSpecStalk_closedPoint
  have hV : gp Y (closedPoint _) ∈ π ⁻¹ᵁ U := by rw [hg]; exact hY
  have hB : ∀ F : Sp Y.functionField ⟶ X, F = gp Y ≫ π → ∀ hU,
      X.presheaf.germ U (F (closedPoint _)) hU ≫ Scheme.stalkClosedPointTo F =
        π.app U ≫ Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) hY := by
    rintro F rfl hU
    rw [Scheme.stalkClosedPointTo_comp]
    refine (Scheme.Hom.germ_stalkMap_assoc π U (gp Y (closedPoint _)) hV _).trans ?_
    exact congrArg (π.app U ≫ ·) (germ_gp (π ⁻¹ᵁ U) hY hV)
  have := (hA _ e hV).symm.trans (hB _ rfl hV)
  exact congrArg (fun g => g.hom s) this

theorem regAt_map (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (θ : X.functionField →+* Y.functionField) (hθ : PFF (𝟙 _) π θ) (y : Y) (u : X.functionField)
    (hu : RegAt (π y) u) : RegAt y (θ u) := by
  obtain ⟨l, hl, e⟩ := hθ
  rw [Category.comp_id] at hl
  subst hl
  obtain ⟨U, hx, s, rfl⟩ := hu.exists_fnOf
  have hy : y ∈ π ⁻¹ᵁ U := hx
  rw [fnOf_map π θ e U _ (gen_mem hy) s]
  exact regAt_fnOf hy _ _

end GlobalTheory.Desc.RegPull
