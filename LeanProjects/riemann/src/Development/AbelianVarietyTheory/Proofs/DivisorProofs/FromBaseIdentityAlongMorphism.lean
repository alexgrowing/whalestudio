import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UChart.FromBaseAlong

theorem gm_comp_map {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U)
    (a : Γ(X, U)ˣ) :
    Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U a) = gm (f ≫ g) z U a := by
  apply Units.ext
  show (f.stalkMap z).hom (gm g (f z) U a).val = _
  rw [← gs_unit (f ≫ g) z U h, ← gs_unit g (f z) U h, ← gs_pull f g z U h, gs_eq f z (g ⁻¹ᵁ U) h, gs_eq g (f z) U h]
  exact Scheme.Hom.germ_stalkMap_apply f (g ⁻¹ᵁ U) z h _

theorem val_comp_map {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y') (g : Y' ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Units.map (r.stalkMap z).hom.toMonoidHom (val t g (r z) (fun ψ => J (r ≫ ψ))) = val t (r ≫ g) z J := by
  rw [val_of t (r ≫ g) z J (fun k => J (r ≫ g ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_comp_map r g z _ (Set.mem_iInter.2 fun k => hJ (r ≫ g ≫ φ k)) _

theorem fromBase_along : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp W₀ ⟶ B₀.left)) (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1])) (β : Q.P.A.left ⟶ B₀.left) (w : LB.Iso Q.P.L (M₀.pull β)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.P.A B₀ (spMap ιb) β ∧ w.IsGen ∧ (∀ a, cpt Q a ≫ β = spMap ιb ≫ c₀ a) ∧ (∀ a b, (τ₁ a b).IsGen) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (a b : Q.X) (zz : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) (J₀ : (Z ⟶ B₀.left) → M₀.ι), Good Q.P.L zz J → Good M₀ zz J₀ → val (τ₀ a b) r zz J = gm (r ≫ cpt Q (a + b)) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q (a + b) ≫ β), J (r ≫ cpt Q (a + b)))) * (gm (r ≫ cpt Q a) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q a ≫ β), J (r ≫ cpt Q a))))⁻¹ * (gm (r ≫ cpt Q b) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q b ≫ β), J (r ≫ cpt Q b))))⁻¹ * gm (r ≫ cpt Q 0) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q 0 ≫ β), J (r ≫ cpt Q 0))) * val (τ₁ a b) (r ≫ spMap ιb) zz J₀ := by
  intro R _ _ Q τ₀ W₀ _ ιb ⟨B₀, i, M₀, c₀, τ₁, β, w, h₁, h₂, h₃, h₄, h₅, h₆, h⟩
  refine ⟨B₀, i, M₀, c₀, τ₁, β, w, h₁, h₂, h₃, h₄, h₅, h₆, fun Z r a b zz J J₀ hJ hJ₀ => ?_⟩
  have e := congrArg (Units.map (r.stalkMap zz).hom.toMonoidHom)
    (h a b (r zz) (fun ψ => J (r ≫ ψ)) (fun ψ => J₀ (r ≫ ψ)) (fun ψ => hJ (r ≫ ψ)) (fun ψ => hJ₀ (r ≫ ψ)))
  have g : ∀ x : Q.X, Units.map (r.stalkMap zz).hom.toMonoidHom
      (gm (cpt Q x) (r zz) _ (w.s (fun _ => J₀ (r ≫ cpt Q x ≫ β), J (r ≫ cpt Q x)))) =
      gm (r ≫ cpt Q x) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q x ≫ β), J (r ≫ cpt Q x))) := fun x =>
    gm_comp_map r (cpt Q x) zz _
      (show cpt Q x (r zz) ∈ (M₀.pull β).U (fun _ => J₀ (r ≫ cpt Q x ≫ β)) ⊓ Q.P.L.U (J (r ≫ cpt Q x)) from
        ⟨Set.mem_iInter.2 fun _ => hJ₀ (r ≫ cpt Q x ≫ β), hJ (r ≫ cpt Q x)⟩) _
  have v₀ := val_comp_map (τ₀ a b) r (𝟙 _) zz hJ
  have v₁ := val_comp_map (τ₁ a b) r (spMap ιb) zz hJ₀
  rw [Category.comp_id] at v₀
  rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv] at e
  exact v₀.symm.trans (e.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (g (a + b)) (congrArg (·⁻¹) (g a))) (congrArg (·⁻¹) (g b))) (g 0)) v₁))

end GlobalTheory.UChart.FromBaseAlong
