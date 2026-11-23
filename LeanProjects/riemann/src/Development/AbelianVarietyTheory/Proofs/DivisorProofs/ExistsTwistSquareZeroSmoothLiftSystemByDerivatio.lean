import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulEqZeroOfMemMap
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.Twist

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}

def twistHom {B B₀ B' : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] [CommRing B']
    [Algebra R B'] (hI : I ^ 2 = 0) (p : B →+* B₀) (hp : SemiHom π p) (α : B →ₐ[R] B') (θ : Ω[B₀⁄R₀] →+ B')
    (hsm : ∀ b w, θ (p b • w) = α b * θ w) (hmem : ∀ w, θ w ∈ I.map (algebraMap R B')) : B →ₐ[R] B' where
  toFun b := α b + θ (D R₀ B₀ (p b))
  map_one' := by simp
  map_mul' b c := by
    have h := mul_eq_zero_of_mem_map hI (hmem (D R₀ B₀ (p b))) (hmem (D R₀ B₀ (p c)))
    simp only [map_mul, Derivation.leibniz, map_add, hsm]
    linear_combination -h
  map_zero' := by simp
  map_add' b c := by simp only [map_add]; abel
  commutes' r := by
    simp only [SemiHom.map_algebraMap hp, Derivation.map_algebraMap, map_zero, add_zero, AlgHom.commutes]

variable {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} (S : Sys I π s₀) (hI : I ^ 2 = 0)
  (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S.F.obj V)
  (hsm : ∀ (U V : AffOp X₀) (a : U ⟶ V) b w, θ U V a (S.p U b • w) = mp S.F a b * θ U V a w)
  (hmem : ∀ (U V : AffOp X₀) (a : U ⟶ V) w, θ U V a w ∈ I.map (algebraMap R (S.F.obj V)))
  (hid : ∀ U, θ U U (𝟙 U) = 0)
  (hcomp : ∀ (U V W : AffOp X₀) (a : U ⟶ V) (b : V ⟶ W) (c : S.F.obj U),
    θ U W (a ≫ b) (D R₀ _ (S.p U c)) =
      mp S.F b (θ U V a (D R₀ _ (S.p U c))) + θ V W b (D R₀ _ (S.p V (mp S.F a c))))

def twistF : AffOp X₀ ⥤ CommAlgCat.{0} R where
  obj := S.F.obj
  map {U V} a := CommAlgCat.ofHom (twistHom hI (S.p U) (S.semi U) (mp S.F a) (θ U V a) (hsm U V a) (hmem U V a))
  map_id U := CommAlgCat.hom_ext (AlgHom.ext fun b ↦ by
    change mp S.F (𝟙 U) b + θ U U (𝟙 U) (D R₀ _ (S.p U b)) = b
    rw [hid, AddMonoidHom.zero_apply, add_zero, mp_id])
  map_comp {U V W} a b := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ by
    change mp S.F (a ≫ b) c + θ U W (a ≫ b) (D R₀ _ (S.p U c)) =
      mp S.F b (mp S.F a c + θ U V a (D R₀ _ (S.p U c))) +
        θ V W b (D R₀ _ (S.p V (mp S.F a c + θ U V a (D R₀ _ (S.p U c)))))
    have h0 : S.p V (θ U V a (D R₀ _ (S.p U c))) = 0 := (S.ker V _).2 (hmem U V a _)
    rw [map_add (S.p V), h0, add_zero, hcomp, mp_comp, map_add]
    abel)

def twistSys : Sys I π s₀ where
  F := twistF S hI θ hsm hmem hid hcomp
  p := S.p
  semi := S.semi
  nat {U V} a b := by
    change S.p V (mp S.F a b + θ U V a (D R₀ _ (S.p U b))) = _
    rw [map_add, (S.ker V _).2 (hmem U V a _), add_zero]
    exact S.nat a b
  surj := S.surj
  ker := S.ker
  smooth := S.smooth

def ev {S' : Sys I π s₀} (v : GlobForm s₀ →+ Z1 S'.F) {U V : AffOp X₀}
    (a : U ⟶ V) : GlobForm s₀ →+ S'.F.obj V where
  toFun w := (v w).1 U V a
  map_zero' := by simp
  map_add' w w' := by simp

end GlobalTheory.LiftSys.Twist

namespace GlobalTheory.LiftSys

open Twist

theorem exists_twist : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (S : Sys I π s₀) (v : GlobForm s₀ →+ Z1 S.F), (∀ w, S.IsIdealValuedLiftSystemCocycle (v w)) → (∀ (r : R) w, v (π r • w) = r • v w) → ∃ (S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ ∧ ∀ (w : GlobForm s₀) U V a, θ U V a (w.1 U) = Φ.φ V ((v w).1 U V a) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar S v hv hs
  have hex : ∀ (U V : AffOp X₀) (a : U ⟶ V), ∃! θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S.F.obj V,
      (∀ b w, θ (S.p U b • w) = mp S.F a b * θ w) ∧ (∀ w, θ w ∈ I.map (algebraMap R (S.F.obj V))) ∧
        ∀ w : GlobForm s₀, θ (w.1 U) = (v w).1 U V a := fun U V a ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar U _ _ (S.p U) (S.semi U) (S.surj U) (S.ker U) (mp S.F a)
      (ev v a) (fun r w ↦ by show (v (π r • w)).1 U V a = r • (v w).1 U V a; rw [hs]; rfl) (fun w ↦ hv w U V a)
  choose θ hθ huniq using hex
  have hsm := fun U V a ↦ (hθ U V a).1
  have hmem := fun U V a ↦ (hθ U V a).2.1
  have hglob := fun U V a ↦ (hθ U V a).2.2
  have hid : ∀ U, θ U U (𝟙 U) = 0 := fun U ↦ (huniq U U (𝟙 U) 0
    ⟨fun b w ↦ by simp, fun w ↦ by simp, fun w ↦ by rw [AddMonoidHom.zero_apply, Z1.id]⟩).symm
  have hcomp' : ∀ (U V W : AffOp X₀) (a : U ⟶ V) (b : V ⟶ W) (x : Ω[Sec s₀ U.unop.1⁄R₀]),
      θ U W (a ≫ b) x = mp S.F b (θ U V a x) + θ V W b (p1 (OAff s₀) a x) := by
    intro U V W a b
    let ψ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S.F.obj W :=
      AddMonoidHom.mk' (fun x ↦ mp S.F b (θ U V a x) + θ V W b (p1 (OAff s₀) a x)) (fun x y ↦ by
        simp only [map_add]; abel)
    have e : ψ = θ U W (a ≫ b) := by
      refine huniq U W (a ≫ b) ψ ⟨fun c x ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩
      · show mp S.F b (θ U V a (S.p U c • x)) + θ V W b (p1 (OAff s₀) a (S.p U c • x)) =
          mp S.F (a ≫ b) c * (mp S.F b (θ U V a x) + θ V W b (p1 (OAff s₀) a x))
        rw [hsm, oneFormsMapOfFunctorMorphism_smul, ← S.nat, hsm, map_mul, mp_comp, mul_add]
      · exact Ideal.add_mem _ (algHom_mem_map I (mp S.F b) (hmem U V a x)) (hmem V W b _)
      · show mp S.F b (θ U V a (w.1 U)) + θ V W b (p1 (OAff s₀) a (w.1 U)) = (v w).1 U W (a ≫ b)
        rw [← w.2 a, hglob, hglob, Z1.comp]
    intro x
    rw [← e]
    rfl
  have hcomp : ∀ (U V W : AffOp X₀) (a : U ⟶ V) (b : V ⟶ W) (c : S.F.obj U),
      θ U W (a ≫ b) (D R₀ _ (S.p U c)) =
        mp S.F b (θ U V a (D R₀ _ (S.p U c))) + θ V W b (D R₀ _ (S.p V (mp S.F a c))) := by
    intro U V W a b c
    rw [hcomp', p1_D, S.nat]
  let S' := twistSys S hI θ hsm hmem hid hcomp
  let Φ : S.LocIso S' := ⟨fun _ ↦ AlgEquiv.refl, fun _ _ ↦ rfl⟩
  refine ⟨S', Φ, θ, fun U V a ↦ ⟨fun b w ↦ ?_, fun b ↦ ?_, hmem U V a⟩, fun w U V a ↦ hglob U V a w⟩
  · show θ U V a (S.p U b • w) = (mp S.F a b + θ U V a (D R₀ _ (S.p U b))) * θ U V a w
    rw [hsm, add_mul, mul_eq_zero_of_mem_map hI (hmem U V a _) (hmem U V a _), add_zero]
  · show θ U V a (D R₀ _ (S.p U b)) = (mp S.F a b + θ U V a (D R₀ _ (S.p U b))) - mp S.F a b
    rw [add_sub_cancel_left]

end GlobalTheory.LiftSys
