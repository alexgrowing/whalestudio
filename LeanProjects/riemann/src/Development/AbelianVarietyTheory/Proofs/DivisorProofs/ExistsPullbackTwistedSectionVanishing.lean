import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem formEq_pull {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a : D.P.A ⟶ D.P.A) (k : ℕ) (α δ : D.X) :
    FormEq (Sum.elim (fun i => a.left ≫ D.famφB α i) (Sum.elim (D.Oφ (𝟙 D.P.A) δ) (D.Oφ a α)))
      (Sum.elim (DegPre.famε k) (Sum.elim Oε Oinvε)) (tφ D a δ) (tε 0 k) := by
  intro U _ h
  have e₁ : a.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left = (padd D.P.A a (toUnit _ ≫ D.c α)).left := by
    rw [← Over.comp_left, padd, padd, ← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
  have e₂ : a.left ≫ (toUnit D.P.A ≫ D.c α).left = (toUnit D.P.A ≫ D.c α).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  have e₃ : a.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (toUnit D.P.A ≫ η[D.P.A]).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, DegPre.famφB,
    DegPre.Oφ, tφ, tε, DegPre.famε, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_succ, e₁, e₂, e₃,
    Category.comp_id, Over.id_left]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_one]
  module

theorem exists_isPullT : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (k : ℕ) (α δ : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α δ)) (f : D.toPre.SecB k α), u.IsGen → ∃ s : SecT D.toPre a 0 k δ, IsPullT u f s ∧ ∀ e, VanMod (maximalIdeal R) f e → Van (maximalIdeal R) s e := by
  intro R _ _ _ _ D a k α δ u f hu
  obtain ⟨s, hs⟩ := exists_sec D.toPre.P.isLB (formEq_pull D.toPre a k α δ) (pullMulSec f a.left u hu)
  have hp : IsPullT u f s := fun Z x z J hJ => (hs Z x z J hJ).trans (sval_pullMulSec f a.left u hu x z hJ)
  refine ⟨s, hp, fun e hb Z x z J hJ => ?_⟩
  obtain ⟨h, hh⟩ : ∃ h : Z ⟶ pullback D.toPre.P.A.hom (thick R (maximalIdeal R) e),
      h ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) =
        (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) ≫ a.left :=
    ⟨pullback.lift _ (x ≫ pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) e)) (by
      rw [Category.assoc, Over.w, Category.assoc, Category.assoc, pullback.condition]), pullback.lift_fst _ _ _⟩
  have z₁ : sval f ((x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) ≫ a.left) z J = 0 := by
    rw [← hh]
    have hm := hJ.mem (D.toPre.famφB α) (h ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e))
    exact (gs_pull h _ z _ hm _).symm.trans ((congrArg (gs h z _) (hb _)).trans (DVR.gs_zero h z _ hm))
  rw [hp Z _ z J hJ, z₁, zero_mul]

end GlobalTheory.TwFam
