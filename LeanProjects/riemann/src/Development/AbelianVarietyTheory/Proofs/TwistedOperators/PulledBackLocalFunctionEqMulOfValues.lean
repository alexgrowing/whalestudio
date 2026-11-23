import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeEx

theorem gs_appLE_top {X Y : Scheme.{0}} (w : Y ⟶ X) (U : X.Opens) (hi : ⊤ ≤ w ⁻¹ᵁ U) (z : Y) (a : Γ(X, U)) :
    gs (𝟙 Y) z ⊤ ((w.appLE U ⊤ hi).hom a) = gs w z U a := by
  rw [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, gs_res (𝟙 Y) z hi trivial,
    gs_pull (𝟙 Y) w z U (hi trivial), Category.id_comp]

theorem appLE_eq_mul_of_sv : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] {x : Sp T ⟶ Xo.X} {k : ℤ} (w : Sp Ω ⟶ Gx x) (t t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))) (α : Ω), (∀ (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP t w z J = gs (𝟙 (Sp Ω)) z ⊤ (toΓ Ω α) * sv Xo.univ.t.G Xo.univ.t.PP t₀ w z J) → ∀ (i : (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).ι) (hi : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i), (w.appLE _ ⊤ hi).hom (t.f i) = toΓ Ω α * (w.appLE _ ⊤ hi).hom (t₀.f i) := by
  intro E _ _ _ H Dw l Xo T Ω _ _ x k w t t₀ α h i hi
  apply fn_ext
  intro z _
  have hw : w z ∈ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i := hi trivial
  have hc : ∀ a b, (fun q => w ≫ (snd (Over.mk x) Xo.univ.t.G).left) a =
      (fun q => w ≫ (snd (Over.mk x) Xo.univ.t.G).left) b → i a = i b := fun a b _ =>
    congrArg i (Subsingleton.elim a b)
  obtain ⟨J, hJ, hJi⟩ := exists_good Xo.univ.t.PP.L Xo.univ.t.PP.isLB z
    (fun q => w ≫ (snd (Over.mk x) Xo.univ.t.G).left) i hc (fun q => Set.mem_iInter.1 hw q)
  have e := h z J hJ
  unfold sv at e
  rw [sval_of t w z J i hJi, sval_of t₀ w z J i hJi] at e
  rw [gs_appLE_top, gs_mul (𝟙 (Sp Ω)) z (⊤ : (Sp Ω).Opens) (show (𝟙 (Sp Ω) : Sp Ω ⟶ Sp Ω) z ∈ (⊤ : (Sp Ω).Opens) from trivial),
    gs_appLE_top]
  exact e

end GlobalTheory.HeckeEx
