import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformizationEndomorphismOfLinear
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam

theorem exists_iota_of_rosati {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a a' : D.P.A ⟶ D.P.A)
    [IsMonHom a] [IsMonHom a'] (hr : RosatiAdj D.P.A D.P.L a a') (α δ : D.X) (hc : D.c δ = D.c α ≫ a') :
    ∃ u : LB.Gen (IotaLB D a α δ), IsIota u := by
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB a a' hr
  have cf : ∀ T, DVR.cP D T δ = DVR.cP D T α ≫ a' := fun T => by
    rw [DVR.cP, hc, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) δ) (D.Oφ a α)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (DVR.prod_neg _ _ (prod_ros a a' (𝟙 D.P.A) (DVR.cP D _ α) h)).trans (Eq.symm ?_)
      refine (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (GlobalTheory.UT.OLinEnd.prod_Oφ D (𝟙 _) δ h)
        (GlobalTheory.UT.OLinEnd.prod_Oφ_inv D a α h)).trans ?_
      rw [cf, Category.id_comp, _root_.mul_comm (DVR.cP D _ α) a, _root_.mul_comm (DVR.cP D _ α ≫ a') (𝟙 _)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ u (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _))
  refine ⟨v, hv, fun Z r z J hJ => ?_⟩
  let T : Over (Spec (CommRingCat.of R)) := Over.mk r
  have C : IsCub (cubV D.cub (T := T) z J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb a a' u hu u₀ (T := T) hJ 1 1 (DVR.cP D _ α)).1
  rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := T) z J 1 (DVR.cP D _ α) = 1 := mul_eq_left.1 e.symm
  have o : (1 : T ⟶ D.P.A).left = r ≫ eSec D.P.A := rfl
  have k : (r ≫ eSec D.P.A) ≫ (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left = (lift (1 : T ⟶ D.P.A) (DVR.cP D T α)).left := by
    rw [← o, ← Over.comp_left, comp_lift, DVR.comp_cP, Category.comp_id]
  rw [vv Z _ z J hJ, val_inv, val_pull hJ, k]
  exact inv_eq_one.2 e'

theorem exists_iota : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ α : D.toPre.X, ∃ u : LB.Gen (IotaLB D.toPre a α (h' α)), IsIota u := by
  intro R _ _ _ _ D a a' h h' hE α
  obtain ⟨h₁, h₂, hr, -, hc, -⟩ := hE
  exact exists_iota_of_rosati D.toPre a a' hr α (h' α) (hc α)

end GlobalTheory.TwFam
