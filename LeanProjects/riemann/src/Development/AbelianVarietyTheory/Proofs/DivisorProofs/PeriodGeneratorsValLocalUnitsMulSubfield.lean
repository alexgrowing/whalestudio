import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseWith
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG.AtPoint

theorem gm_stalkMap {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (a : Γ(X, U)ˣ) :
    Units.map (r.stalkMap z).hom.toMonoidHom (gm f (r z) U a) = gm (r ≫ f) z U a := by
  by_cases h : f (r z) ∈ U
  · apply Units.ext
    rw [Units.coe_map, gm_val f (r z) U h, gm_val (r ≫ f) z U h]
    exact Scheme.Hom.germ_stalkMap_apply r (f ⁻¹ᵁ U) z h _
  · have h' : (r ≫ f) z ∉ U := h
    rw [gm, dif_neg h, gm, dif_neg h']
    simp

theorem val_stalkMap {X Y Y' Z : Scheme.{0}} {L : LB X} {Ix : Type} [Fintype Ix] {φ : Ix → (Y ⟶ X)} {ε : Ix → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (g : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι) :
    Units.map (r.stalkMap z).hom.toMonoidHom (val t g (r z) (fun ψ => J (r ≫ ψ))) = val t (r ≫ g) z J := by
  rw [val_of t (r ≫ g) z J (fun k => J (r ≫ g ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_stalkMap r g z _ _

end GlobalTheory.USep.EvG.AtPoint

open GlobalTheory.USep.EvG.AtPoint in
theorem GlobalTheory.USep.EvG.fromBase_tau_val : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ a b : D.X, ∃ c ∈ k₀, (val (τ₀ a b) (spMap ev) z J).val =
      (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c (a + b)).left) * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ *
        (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c b).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c 0).left)).val * toStk z c := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ _ hk z J J₀ hJ hJ₀ a b
  obtain ⟨-, -, -, -, -, -, hlast⟩ := hFB
  have hJ' : Good D.P.L ((spMap ev) z) (fun ψ => J (spMap ev ≫ ψ)) := fun ψ => hJ (spMap ev ≫ ψ)
  have hJ₀' : Good M₀ ((spMap ev) z) (fun ψ => J₀ (spMap ev ≫ ψ)) := fun ψ => hJ₀ (spMap ev ≫ ψ)
  have E := congrArg (Units.map ((spMap ev).stalkMap z).hom.toMonoidHom) (hlast a b ((spMap ev) z) _ _ hJ' hJ₀')
  simp only [map_mul, map_inv, val_stalkMap, gm_stalkMap, Category.comp_id] at E
  have hg : ∀ x : D.X, gm (spMap ev ≫ UChart.cpt D x) z
      (((M₀.pull β).div D.P.L).U (fun _ => J₀ (spMap ev ≫ UChart.cpt D x ≫ β), J (spMap ev ≫ UChart.cpt D x)))
      (w.s (fun _ => J₀ (spMap ev ≫ UChart.cpt D x ≫ β), J (spMap ev ≫ UChart.cpt D x))) =
      GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c x).left) := by
    intro x
    show _ = gw w _ z _ _
    rw [Category.assoc]
    rfl
  rw [hg (a + b), hg a, hg b, hg 0, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp] at E
  obtain ⟨c, hc, hv⟩ := GlobalTheory.Poinc.Sep.val_spMap_mem k₀ (τ₁ a b) (ev.comp ib) hk z hJ₀
  refine ⟨c, hc, ?_⟩
  rw [E, Units.val_mul, hv]
