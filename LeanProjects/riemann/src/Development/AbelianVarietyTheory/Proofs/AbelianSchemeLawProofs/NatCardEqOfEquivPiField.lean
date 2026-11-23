import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace MulLaw

theorem natCard_eq_of_equiv_pi_field {R : Type} [Field R] {U V : Type} [AddCommGroup U]
    [Module R U] [AddCommGroup V] [Module R V] {X : Type} (e : U ≃ₗ[R] (X → V)) {m : ℕ}
    (hm : 0 < m) (hU : Module.finrank R U = m) (hV : Module.finrank R V = 1) :
    Nat.card X = m := by
  classical
  haveI : Module.Finite R U := Module.finite_of_finrank_pos (hU ▸ hm)
  haveI : Module.Finite R V := Module.finite_of_finrank_pos (hV ▸ Nat.one_pos)
  have e₁ : V ≃ₗ[R] R := LinearEquiv.ofFinrankEq V R (by rw [hV, Module.finrank_self])
  have e₂ : U ≃ₗ[R] (X → R) := e.trans (LinearEquiv.piCongrRight fun _ => e₁)
  haveI : Module.Finite R (X → R) := Module.Finite.equiv e₂
  haveI : Finite X := (Pi.linearIndependent_single_one X R).finite
  haveI := Fintype.ofFinite X
  rw [← hU, e₂.finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

theorem natCard_eq_of_equiv_pi {R : Type} [CommRing R] (hR : IsField R) {U V : Type}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V] {X : Type}
    (e : U ≃ₗ[R] (X → V)) {m : ℕ}
    (hm : 0 < m) (hU : Module.finrank R U = m) (hV : Module.finrank R V = 1) :
    Nat.card X = m := by
  letI := hR.toField
  exact natCard_eq_of_equiv_pi_field e hm hU hV

noncomputable def basePointsEquiv {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'}
    [GrpObj A] [GrpObj A'] {g : A'.left ⟶ A.left} (hg : IsPullback g A'.hom A.hom f)
    (hmul : ∀ (T : Over S') (x y : T ⟶ A'),
      toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y) (T : Over S') :
    (T ⟶ A') ≃* (Over.mk (T.hom ≫ f) ⟶ A) where
  toFun x := toBase hg.w x
  invFun y := Over.homMk (hg.lift y.left T.hom (Over.w y)) (hg.lift_snd _ _ _)
  left_inv x := by
    apply Over.OverMorphism.ext
    apply hg.hom_ext
    · exact hg.lift_fst _ _ _
    · exact (hg.lift_snd _ _ _).trans (Over.w x).symm
  right_inv y := by
    apply Over.OverMorphism.ext
    exact hg.lift_fst _ _ _
  map_mul' x y := hmul T x y

end MulLaw

theorem mulN_of_decomposition :
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n j : ℕ), (n : K) ≠ 0 → 1 ≤ j → Nonempty (SecM P.A P.L ((n ^ 2 * j : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K))) ≃ₗ[Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)] ({x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ n = 1} → SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K)))))) → GlobalSectionsRankAlgClosed → PolBaseChangeSt → MulNSt := by
  intro hQ hRel hH hBC S _ P n hn
  obtain ⟨h1, h2, h3, h4⟩ := hQ S P n hn
  refine ⟨h1, h2, h3, h4, fun k _ _ t hk => ?_⟩
  obtain ⟨P', g, hg, hdim, hmul, -⟩ := hBC S _ t P
  obtain ⟨e⟩ := hRel k P' n 1 hk le_rfl
  have hn2 : 1 ≤ n ^ 2 * 1 := by
    rw [Nat.mul_one]; exact Nat.one_le_pow _ _ hn
  have hU := hH k P' (n ^ 2 * 1) hn2
  have hV := hH k P' 1 le_rfl
  rw [one_pow] at hV
  have hF : IsField Γ((baseOver (Spec (CommRingCat.of k))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)
  have hcard := MulLaw.natCard_eq_of_equiv_pi hF e (Nat.pow_pos hn2) hU hV
  have φ : (baseOver (Spec (CommRingCat.of k)) ⟶ P'.A) ≃* (Over.mk t ⟶ P.A) := by
    have ψ := MulLaw.basePointsEquiv hg hmul (baseOver (Spec (CommRingCat.of k)))
    have ht : (baseOver (Spec (CommRingCat.of k))).hom ≫ t = t := Category.id_comp t
    rw [ht] at ψ
    exact ψ
  rw [← Nat.card_congr (φ.toEquiv.subtypeEquiv
    (p := fun x => x ^ n = 1) (q := fun x => x ^ n = 1) (fun x => by
      show x ^ n = 1 ↔ φ x ^ n = 1
      rw [← map_pow, map_eq_one_iff φ φ.injective])), hcard, hdim, Nat.mul_one, ← pow_mul]

end GlobalTheory
