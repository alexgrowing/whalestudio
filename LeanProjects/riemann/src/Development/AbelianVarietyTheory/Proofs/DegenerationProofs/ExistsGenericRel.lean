import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenericFibreIsoOfCompatibleThickenings

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericIso

open GlobalTheory.RigidGeneric GlobalTheory.SecRingIso ReciprocityTheory.ChartRestriction.G.DVR in

theorem exists_genericRel : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), GlobalTheory.GenericIso.LevelIso U.toUnifPre U'.toUnifPre hD j → GlobalTheory.GenericIso.Enough U.toUnifPre U'.toUnifPre hD j → ∃ (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))), GlobalTheory.GenericIso.GenericRel U.toUnifPre U'.toUnifPre hD j Φ w := by
  intro hL R _ _ I hI D D' A A' G G' _ _ _ _ hG hG' U U' hD j _ en
  obtain ⟨w, v, hw, hv, -, lf⟩ := exists_compare U
  obtain ⟨w', v', hw', hv', e', lf'⟩ := exists_compare U'
  have jac : I ≤ Ideal.jacobson ⊥ := by
    have := hI.2.2.2
    exact IsAdicComplete.le_jacobson_bot I
  have := hI.1
  have := hG.smooth
  have := hG'.smooth
  have := hG.geomConnected
  have := hG'.geomConnected
  let Ag : ∀ k, H0 U'.LG.L k → H0 U.LG.L k → Prop := fun k σ' σ => ∀ e,
    Agr (W := (thickObj R I e G').left) (Idx := D.toPre.P.L.ι × D'.toPre.P.L.ι)
      ((j e).hom.left ≫ (fstG I e G).left) (fstG I e G').left
      (fun y i => (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y) ∈
        D.toPre.P.L.U i.1 ∧ (U'.gt e).pG.left y ∈ D'.toPre.P.L.U i.2)
      (fun Z r z i jL => Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z i.1 (fun _ => jL))
      (fun Z r z i jL => Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z i.1 i.2 * Geo.Tor.gw (U'.w e) r z i.2 (fun _ => jL))
      σ σ'
  have ov : ∀ e, ((j e).hom.left ≫ (fstG I e G).left) ≫ G.hom = (fstG I e G').left ≫ G'.hom := fun e =>
    (Category.assoc _ _ _).trans ((congrArg ((j e).hom.left ≫ ·) (Over.w (fstG I e G))).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ thick R I e) (Over.w (j e).hom))).trans
        (Over.w (fstG I e G')).symm))
  have cov : ∀ e (y : (thickObj R I e G').left), ∃ i : D.toPre.P.L.ι × D'.toPre.P.L.ι,
      (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y) ∈
        D.toPre.P.L.U i.1 ∧ (U'.gt e).pG.left y ∈ D'.toPre.P.L.U i.2 := fun e y => by
    obtain ⟨a, ha⟩ := exists_chart D.toPre.P.isLB
      ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y))
    obtain ⟨b, hb⟩ := exists_chart D'.toPre.P.isLB ((U'.gt e).pG.left y)
    exact ⟨(a, b), ha, hb⟩
  obtain ⟨Φ, w₀, h₀, H⟩ := exists_iso_of_rel hL G.hom G'.hom U.LG.isLB U'.LG.isLB A A' (gen_over' U) (gen_over' U')
    (gen_injective U) (gen_injective U') hv hv' lf lf' Ag
    (fun k c s' s t' t d' d h h' f' f e => (h e).comb (ov e) (h' e) f f')
    (fun n m s' s t' t d' d h h' f' f e => (h e).mul (h' e) f f')
    (fun k s' s h => ⟨fun f => funext ((sec_eq_zero_and_hom_eq_of_thickenings R I jac G).1 _
        (linComb_isLB _ U.LG.isLB _ _) s fun e J => by
          have : IsIso (j e).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (j e).hom))
          exact (ConcreteCategory.bijective_of_isIso ((j e).hom.left.app _)).1
            (((h e).zero U'.LG.isLB (cov e) f J).trans (map_zero _).symm)),
      fun f => funext ((sec_eq_zero_and_hom_eq_of_thickenings R I jac G').1 _
        (linComb_isLB _ U'.LG.isLB _ _) s' fun e J => (h e).symm.zero U.LG.isLB (cov e) f J)⟩)
    (fun k hk s => by
      obtain ⟨c, t', t, hc, h₁, h₂⟩ := (en k hk).1 s
      exact ⟨c, hc, t', t, fun e Z r z i a b hC => h₂ e Z r z i.1 i.2 a b hC.1 hC.2, funext h₁⟩)
    (fun k hk s => by
      obtain ⟨c, t', t, hc, h₁, h₂⟩ := (en k hk).2 s
      exact ⟨c, hc, t', t, fun e Z r z i a b hC => h₂ e Z r z i.1 i.2 a b hC.1 hC.2, funext h₁⟩)
  obtain ⟨u, hu, K⟩ := exists_move U.LG.isLB U'.LG.isLB A.isLB A'.isLB (gen_inv U') hv h₀ hw' e'
    ((U'.gen ≪≫ Φ ≪≫ U.gen.symm).hom.left ≫ pullback.fst G.hom (jK R))
    ((Category.assoc _ _ _).trans (congrArg (U'.gen.hom.left ≫ ·) (Category.assoc _ _ _)))
  refine ⟨U'.gen ≪≫ Φ ≪≫ U.gen.symm, u, hu, fun k hk σ' σ h => ?_⟩
  obtain ⟨a, ha⟩ := exists_pulls U.LG.isLB A.isLB hv σ
  obtain ⟨a', ha'⟩ := exists_pulls U'.LG.isLB A'.isLB hv' σ'
  exact K k σ σ' a a' ha
    (H k hk σ' σ a' a (fun e Z r z i a b hC => h e Z r z i.1 i.2 a b hC.1 hC.2) ha' ha) ha'

end GlobalTheory.GenericIso
