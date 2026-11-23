import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAffineWeightUnits

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU
namespace TorsionCount

theorem card_torsion_eq_mul {A B : Type} [CommGroup A] [CommGroup B] (f : A →* B) (N : ℕ)
    (h : ∀ b : B, b ^ N = 1 → ∃ a : A, a ^ N = 1 ∧ f a = b) :
    Nat.card {a : A // a ^ N = 1} = Nat.card {a : A // a ^ N = 1 ∧ f a = 1} * Nat.card {b : B // b ^ N = 1} := by
  choose s hs hs' using h
  rw [← Nat.card_prod]
  have hf : ∀ a : A, a ^ N = 1 → f a ^ N = 1 := fun a ha => by rw [← map_pow, ha, map_one]
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : {a : A // a ^ N = 1 ∧ f a = 1} × {b : B // b ^ N = 1} =>
      (⟨x.1.1 * s x.2.1 x.2.2, by rw [mul_pow, x.1.2.1, hs, _root_.one_mul]⟩ : {a : A // a ^ N = 1})) ⟨?_, ?_⟩).symm
  · rintro ⟨⟨a, ha⟩, b, hb⟩ ⟨⟨a', ha'⟩, b', hb'⟩ e
    have e₁ : a * s b hb = a' * s b' hb' := congrArg Subtype.val e
    have e₂ := congrArg f e₁
    rw [map_mul, map_mul, hs', hs', ha.2, ha'.2, _root_.one_mul, _root_.one_mul] at e₂
    subst e₂
    have e₃ := mul_right_cancel e₁
    subst e₃
    rfl
  · rintro ⟨a, ha⟩
    refine ⟨(⟨a * (s (f a) (hf a ha))⁻¹, ?_, ?_⟩, ⟨f a, hf a ha⟩), Subtype.ext (inv_mul_cancel_right _ _)⟩
    · rw [mul_pow, inv_pow, ha, hs, inv_one, _root_.one_mul]
    · rw [map_mul, map_inv, hs', mul_inv_cancel]

theorem card_hom_torsion {X U : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [CommGroup U] (N : ℕ) :
    Nat.card {φ : Multiplicative X →* U // φ ^ N = 1} = Nat.card {u : U // u ^ N = 1} ^ Module.finrank ℤ X := by
  let e := Module.finBasis ℤ X
  have key : Function.Bijective (fun (φ : {φ : Multiplicative X →* U // φ ^ N = 1}) (k : Fin (Module.finrank ℤ X)) =>
      (⟨φ.1 (Multiplicative.ofAdd (e k)), DFunLike.congr_fun φ.2 _⟩ : {u : U // u ^ N = 1})) := by
    have ext : ∀ φ ψ : Multiplicative X →* U,
        (∀ k, φ (Multiplicative.ofAdd (e k)) = ψ (Multiplicative.ofAdd (e k))) → φ = ψ := fun φ ψ h => by
      have : (MonoidHom.toAdditiveRight φ).toIntLinearMap = (MonoidHom.toAdditiveRight ψ).toIntLinearMap :=
        e.ext fun k => congrArg Additive.ofMul (h k)
      exact MonoidHom.ext fun χ => congrArg Additive.toMul (LinearMap.congr_fun this (Multiplicative.toAdd χ))
    constructor
    · intro φ ψ h
      exact Subtype.ext (ext _ _ fun k => congrArg Subtype.val (congrFun h k))
    · intro v
      let l : X →ₗ[ℤ] Additive U := e.constr ℤ fun k => Additive.ofMul (v k).1
      have hl : ∀ k, AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom (Multiplicative.ofAdd (e k)) = (v k).1 :=
        fun k => congrArg Additive.toMul (e.constr_basis ℤ _ k)
      refine ⟨⟨AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom, ext _ _ fun k => ?_⟩,
        funext fun k => Subtype.ext (hl k)⟩
      rw [MonoidHom.pow_apply, hl, (v k).2, MonoidHom.one_apply]
  rw [Nat.card_congr (Equiv.ofBijective _ key), Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

theorem card_units_torsion (K : Type) [Field K] [IsAlgClosed K] {N : ℕ} (hN : (N : K) ≠ 0) :
    Nat.card {u : Kˣ // u ^ N = 1} = N := by
  have : NeZero (N : K) := ⟨hN⟩
  have : NeZero N := NeZero.of_neZero_natCast K
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity K N

theorem card_torsion_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) (N : ℕ) :
    Nat.card {a : A // a ^ N = 1} = Nat.card {b : B // b ^ N = 1} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun a => by
    rw [← e.map_eq_one_iff, map_pow]; rfl)

end TorsionCount

open TorsionCount in

theorem torusQuotient_card_torsion :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G]
      [IsCommMonObj G] (Q : TQ G X) (K : Type) [Field K] [IsAlgClosed K] (p : Spec (CommRingCat.of K) ⟶ S) (N : ℕ),
      (N : K) ≠ 0 → Nat.card {x : Over.mk p ⟶ G // x ^ N = 1 ∧ x ≫ Q.q = 1} = N ^ Module.finrank ℤ X ∧
        Nat.card {x : Over.mk p ⟶ G // x ^ N = 1} =
          N ^ Module.finrank ℤ X * Nat.card {b : Over.mk p ⟶ Q.B // b ^ N = 1} := by
  intro S X _ _ _ G _ _ Q K _ _ p N hN
  have := Q.q_hom
  have := Q.i_hom
  have hN' : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact hN Nat.cast_zero)
  let e : Kˣ ≃* Γ(Spec (CommRingCat.of K), ⊤)ˣ :=
    Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.toMulEquiv
  have inj : ∀ t t' : Over.mk p ⟶ splitTorus S X, t ≫ Q.i = t' ≫ Q.i → t = t' := fun t t' h =>
    Q.isKernel.hom_ext h (toUnit_unique _ _)
  have h₃ : ∀ t : Over.mk p ⟶ splitTorus S X, (t ≫ Q.i) ≫ Q.q = 1 := fun t => by
    rw [Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (t ≫ toUnit _) (toUnit _)]
  have key : Function.Bijective (fun t : {t : Over.mk p ⟶ splitTorus S X // t ^ N = 1} =>
      (⟨t.1 ≫ Q.i, by rw [← MonObj.pow_comp, t.2, MonObj.one_comp], h₃ _⟩ :
        {x : Over.mk p ⟶ G // x ^ N = 1 ∧ x ≫ Q.q = 1})) := by
    refine ⟨fun t t' h => Subtype.ext (inj _ _ (congrArg Subtype.val h)), ?_⟩
    rintro ⟨x, hx, hq⟩
    have h₁ : x ≫ Q.q = toUnit _ ≫ η[Q.B] := hq.trans Hom.one_def
    refine ⟨⟨Q.isKernel.lift _ _ h₁, inj _ _ ?_⟩, Subtype.ext (Q.isKernel.lift_fst _ _ _)⟩
    rw [MonObj.pow_comp, IsPullback.lift_fst, hx, MonObj.one_comp]
  have c₁ : Nat.card {x : Over.mk p ⟶ G // x ^ N = 1 ∧ x ≫ Q.q = 1} = N ^ Module.finrank ℤ X := by
    rw [← Nat.card_congr (Equiv.ofBijective _ key), card_torsion_congr (splitTorusPointsEquiv S X (Over.mk p)) N,
      card_hom_torsion]
    exact congrArg (· ^ _) ((card_torsion_congr e N).symm.trans (card_units_torsion K hN))
  refine ⟨c₁, ?_⟩
  rw [← c₁]
  refine card_torsion_eq_mul (MonoidHom.mk' (fun x : Over.mk p ⟶ G => x ≫ Q.q) fun x y => MonObj.mul_comp _ _ _) N
    ((torusQuotient_points_lift S X G Q K p).2 N fun a => ?_)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (a : K) hN'
  have h0 : r ≠ 0 := by
    rintro rfl
    exact a.ne_zero (hr.symm.trans (zero_pow hN'.ne'))
  exact ⟨Units.mk0 r h0, Units.ext (by simpa using hr)⟩

end GlobalTheory.UU
