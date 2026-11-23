import Mathlib
import GroundTheory.TateCohomology.TateTheorem
import GroundTheory.TateCohomology.TateCupUnit
set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory Limits Rep

namespace GroundTheory.GroupCoh

section Transport

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem tateCup_eqToHom_left {A B : Rep.{u} k G} {p p' q r r' : ℤ} (hp : p = p') (hr : r = r')
    (h : p + q = r) (h' : p' + q = r') (a : tateCohomology A p) (b : tateCohomology B q) :
    (eqToHom (congrArg (tateCohomology (A ⊗ B)) hr)).hom (tateCup p q A B r h a b) =
      tateCup p' q A B r' h' ((eqToHom (congrArg (tateCohomology A) hp)).hom a) b := by
  subst hp hr
  simp

theorem eqToHom_tateMap_apply {X Y : Rep.{u} k G} (f : X ⟶ Y) {i j : ℤ} (hij : i = j)
    (x : tateCohomology X i) :
    (eqToHom (congrArg (tateCohomology Y) hij)).hom (((tateCohomologyFunctor i).map f).hom x) =
      ((tateCohomologyFunctor j).map f).hom ((eqToHom (congrArg (tateCohomology X) hij)).hom x) := by
  subst hij
  simp

theorem tateIsoH_eqToHom_apply (A : Rep.{u} k G) {p₀ p p' : ℤ} (n : ℕ) [NeZero n] (e : p₀ = p)
    (e' : p₀ = p') (hp : p = n) (hp' : p' = n) (w : tateCohomology A p₀) :
    (tateIsoH A p n hp).hom.hom ((eqToHom (congrArg (tateCohomology A) e)).hom w) =
      (tateIsoH A p' n hp').hom.hom ((eqToHom (congrArg (tateCohomology A) e')).hom w) := by
  subst e e'
  rfl

end Transport

section Tate

variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
  (S : Subgroup G) [Fintype S]

noncomputable def tateResClass : tateCohomology (res S.subtype M) 2 :=
  (tateIsoH (res S.subtype M) 2 2 (by norm_num)).inv.hom
    (groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u)

variable (h1 : ∀ S : Subgroup G, IsZero (groupCohomology (res S.subtype M) 1))
  (h2 : ∀ S : Subgroup G,
    addOrderOf (groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u) = Nat.card S)
  (h3 : ∀ (S : Subgroup G) (y : groupCohomology (res S.subtype M) 2),
    ∃ m : ℤ, y = m • groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u)

include h1 h2 h3

theorem tateTheorem_δ_δ_tateOne :
    (eqToHom (congrArg (tateCohomology (res S.subtype M)) (show (0 : ℤ) + 1 + 1 = 2 by norm_num))).hom
      ((TateCohomology.δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) (0 + 1)).hom
        ((TateCohomology.δ (augTrivSES_res_shortExact ℤ S.subtype) 0).hom (tateOne ℤ S))) =
      tateResClass M u S := by
  apply moduleIso_hom_injective (tateIsoH (res S.subtype M) 2 2 (by norm_num))
  rw [tateResClass, Iso.inv_hom_id_apply]
  refine (tateIsoH_eqToHom_apply (res S.subtype M) 2 (show (0 : ℤ) + 1 + 1 = 2 by norm_num)
    (show (0 : ℤ) + 1 + 1 = 0 + 2 by norm_num) (by norm_num) (by norm_num) _).trans ?_
  exact tateTheoremIso_zero_apply M u h1 h2 h3 S

set_option maxHeartbeats 1600000 in

theorem tateTheoremIso_hom_apply (n : ℤ) (x : tateCohomology (Rep.trivial ℤ S ℤ) n) :
    (tateTheoremIso M u h1 h2 h3 S n).hom.hom x =
      ((tateCohomologyFunctor (n + 2)).map (ρ_ (res S.subtype M)).hom).hom
        (tateCup 2 n (res S.subtype M) (Rep.trivial ℤ S ℤ) (n + 2) (add_comm 2 n)
          (tateResClass M u S) x) := by
  have hE1 := augTrivSES_res_shortExact ℤ S.subtype
  have hE2 := (shortExact_res S.subtype).2 (splittingSES_shortExact M u)
  have hE1R := shortExact_tensorRight_unit hE1
  have hE2R := shortExact_tensorRight_unit hE2
  have hx : ((tateCohomologyFunctor n).map (ρ_ (𝟙_ (Rep ℤ S))).hom).hom
      (tateCup 0 n (𝟙_ (Rep ℤ S)) (𝟙_ (Rep ℤ S)) n (zero_add n) (tateOne ℤ S) x) = x := by
    rw [← unitors_equal]
    exact leftUnitor_tateCup_tateOne n _ x
  have s1 : (TateCohomology.δ hE1 n).hom x =
      ((tateCohomologyFunctor (n + 1)).map (ρ_ (res S.subtype (augIdeal ℤ G))).hom).hom
        (tateCup (0 + 1) n (res S.subtype (augIdeal ℤ G)) (𝟙_ (Rep ℤ S)) (n + 1) (by omega)
          ((TateCohomology.δ hE1 0).hom (tateOne ℤ S)) x) :=
    (congrArg (TateCohomology.δ hE1 n).hom hx.symm).trans ((δ_rightUnitor_apply hE1 hE1R n _).trans
      (congrArg _ (tateCup_δ_left hE1 (𝟙_ (Rep ℤ S)) hE1R 0 n n (zero_add n) (tateOne ℤ S) x)))
  have s2 : (TateCohomology.δ hE2 (n + 1)).hom
      (((tateCohomologyFunctor (n + 1)).map (ρ_ (res S.subtype (augIdeal ℤ G))).hom).hom
        (tateCup (0 + 1) n (res S.subtype (augIdeal ℤ G)) (𝟙_ (Rep ℤ S)) (n + 1) (by omega)
          ((TateCohomology.δ hE1 0).hom (tateOne ℤ S)) x)) =
      ((tateCohomologyFunctor (n + 1 + 1)).map (ρ_ (res S.subtype M)).hom).hom
        (tateCup (0 + 1 + 1) n (res S.subtype M) (𝟙_ (Rep ℤ S)) (n + 1 + 1) (by omega)
          ((TateCohomology.δ hE2 (0 + 1)).hom ((TateCohomology.δ hE1 0).hom (tateOne ℤ S))) x) :=
    (δ_rightUnitor_apply hE2 hE2R (n + 1) _).trans
      (congrArg _ (tateCup_δ_left hE2 (𝟙_ (Rep ℤ S)) hE2R (0 + 1) n (n + 1) (by omega) _ x))
  have hT : (tateTheoremIso M u h1 h2 h3 S n).hom.hom x =
      (eqToHom (congrArg (tateCohomology (res S.subtype M)) (show n + 1 + 1 = n + 2 by ring))).hom
        ((TateCohomology.δ hE2 (n + 1)).hom ((TateCohomology.δ hE1 n).hom x)) := rfl
  rw [hT, s1, s2]
  refine (eqToHom_tateMap_apply (ρ_ (res S.subtype M)).hom (show n + 1 + 1 = n + 2 by ring) _).trans ?_
  refine congrArg _ ((tateCup_eqToHom_left (show (0 : ℤ) + 1 + 1 = 2 by norm_num)
    (show n + 1 + 1 = n + 2 by ring) _ (add_comm 2 n) _ x).trans ?_)
  exact congrArg (fun t => tateCup 2 n (res S.subtype M) (Rep.trivial ℤ S ℤ) (n + 2) (add_comm 2 n) t x)
    (tateTheorem_δ_δ_tateOne M u S h1 h2 h3)

end Tate

end GroundTheory.GroupCoh
