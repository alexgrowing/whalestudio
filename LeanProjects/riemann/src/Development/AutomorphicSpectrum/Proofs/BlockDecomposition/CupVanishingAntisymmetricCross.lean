import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IotaQInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf

namespace GlobalTheory.CompanionTheory.WedgeOf

theorem cup_add_cup_swap {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (a b : H1 F) : cup F a b + cup F b a = 0 := by
  obtain ⟨a', rfl⟩ := H1.mk_surjective F a
  obtain ⟨b', rfl⟩ := H1.mk_surjective F b
  rw [cup_mk, cup_mk, ← map_add, H2.mk_eq_zero]
  refine ⟨-(fun T T' φ => a'.1 T T' φ * b'.1 T T' φ), ?_⟩
  funext T T' T'' φ ψ
  simp only [map_neg, Pi.neg_apply, d1_apply, Submodule.coe_add, Pi.add_apply, cupZ_apply, Z1.comp, map_mul]
  ring

theorem hopf_pull_lift_cup {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) {D : Type} [Category.{0} D] (G : D ⥤ CommAlgCat.{0} R)
    (π : CoefMap (RingHom.id R) (box F) G) (m : CoefMap (RingHom.id R) F G)
    (hm : ∀ c, m.pull1 c = π.pull1 ((boxL F).pull1 c + (boxR F).pull1 c))
    (t : H1 F ⊗[R] H1 F) :
    m.pull2 (TensorProduct.lift (cup F) t) =
      π.pull2 ((boxL F).pull2 (TensorProduct.lift (cup F) t) +
        (boxR F).pull2 (TensorProduct.lift (cup F) t) +
        TensorProduct.lift (crossB F) (t - TensorProduct.comm R _ _ t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.lift.tmul, CoefMap.pullCohomologyTwo_cup m a b, hm a, hm b, ← CoefMap.pullCohomologyTwo_cup π _ _]
    refine congrArg (fun x => π.pull2 x) ?_
    rw [CoefMap.pullCohomologyTwo_cup (boxL F) a b, CoefMap.pullCohomologyTwo_cup (boxR F) a b, TensorProduct.comm_tmul, map_sub,
      TensorProduct.lift.tmul, TensorProduct.lift.tmul, crossB_apply, crossB_apply]
    simp only [map_add, LinearMap.add_apply]
    have h := cup_add_cup_swap (box F) ((boxL F).pull1 b) ((boxR F).pull1 a)
    have h3 : cup (box F) ((boxR F).pull1 a) ((boxL F).pull1 b) =
        -cup (box F) ((boxL F).pull1 b) ((boxR F).pull1 a) :=
      eq_neg_iff_add_eq_zero.2 (by rw [add_comm]; exact h)
    rw [h3]
    abel
  | add x y hx hy =>
    simp only [map_add, map_sub, hx, hy]
    abel

theorem hopf_cross_antisymm : LowSt → ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R), Hopf F False → ∀ t : H1 F ⊗[R] H1 F,
    TensorProduct.lift (cup F) t = 0 →
      TensorProduct.lift (crossB F) (t - TensorProduct.comm R _ _ t) = 0 := by
  intro hLow R _ C _ F hH t ht
  obtain ⟨D, _, G, π, m, hq, hm, -⟩ := hH
  have h2 := hopf_pull_lift_cup F G π m hm t
  simp only [ht, map_zero, zero_add] at h2
  obtain ⟨-, hinj, -⟩ := hLow R (C × C) D (box F) G π hq
  apply hinj.1
  rw [map_zero]
  exact h2.symm

end GlobalTheory.CompanionTheory.WedgeOf
