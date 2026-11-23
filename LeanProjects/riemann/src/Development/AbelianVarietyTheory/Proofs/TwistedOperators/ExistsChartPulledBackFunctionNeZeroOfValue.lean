import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeEx

theorem exists_appLE_ne_zero_of_sv_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [Field Ω] {x : Sp T ⟶ Xo.X} {k : ℤ} (w : Sp Ω ⟶ Gx x) (t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))) (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP t₀ w z J ≠ 0 → ∃ (i : (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).ι) (hi : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i), (w.appLE _ ⊤ hi).hom (t₀.f i) ≠ 0 := by
  intro E _ _ _ H Dw l Xo T Ω _ _ x k w t₀ z J hJ hne
  refine ⟨fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left), ?_, ?_⟩
  · intro y _
    have hy : y = z := Subsingleton.elim _ _
    subst hy
    exact hJ.mem (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) w
  · intro hi
    have hz : w z ∈ LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left)
        (fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left)) :=
      hJ.mem (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) w
    apply hne
    rw [sv, sval_of t₀ w z J (fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left)) (fun _ => rfl)]
    erw [gs_eq w z _ hz]
    have hle : (⊤ : (Sp Ω).Opens) ≤ w ⁻¹ᵁ LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left)
        (fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left)) := by
      intro y _
      have hy : y = z := Subsingleton.elim _ _
      subst hy
      exact hz
    rw [← TopCat.Presheaf.germ_res_apply (Sp Ω).presheaf (homOfLE hle) z trivial]
    refine (congrArg ((Sp Ω).presheaf.germ ⊤ z trivial).hom ?_).trans (map_zero _)
    exact hi

end GlobalTheory.HeckeEx
