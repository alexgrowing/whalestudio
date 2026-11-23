import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FormalOrigin

def iterOp {A : Type} {n : ℕ} (ds : Fin n → A → A) (α : Fin n →₀ ℕ) (f : A) : A :=
  (List.finRange n).foldr (fun i g => (ds i)^[α i] g) f

def taylor {A B : Type} [CommRing A] [CommRing B] [Algebra ℚ B] {n : ℕ} (ev : A →+* B) (ds : Fin n → A → A)
    (f : A) : MvPowerSeries (Fin n) B :=
  fun α => (∏ i, ((α i).factorial : ℚ))⁻¹ • ev (iterOp ds α f)

section Origin
variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]

def origin : G.left := (η[G]).left (IsLocalRing.closedPoint R)

def evO : G.left.presheaf.stalk (origin G) →+* R :=
  (Scheme.stalkClosedPointTo (R := CommRingCat.of R) (η[G]).left).hom

def constO : R →+* G.left.presheaf.stalk (origin G) :=
  (G.left.presheaf.germ ⊤ (origin G) trivial).hom.comp
    ((G.hom.appLE ⊤ ⊤ (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
end Origin

def intDer {S A : Type} [CommRing S] [CommRing A] [Algebra S A] (δ : Derivation S A A) : Derivation ℤ A A where
  toFun := δ
  map_add' := map_add δ
  map_smul' m x := by simpa using map_zsmul δ m x
  map_one_eq_zero' := δ.map_one_eq_zero
  leibniz' := δ.leibniz

@[simp] theorem intDer_apply {S A : Type} [CommRing S] [CommRing A] [Algebra S A] (δ : Derivation S A A) (a : A) :
    intDer δ a = δ a := rfl

theorem iterOp_zero {A : Type} {n : ℕ} (ds : Fin n → A → A) (f : A) : iterOp ds 0 f = f := by
  unfold iterOp
  induction (List.finRange n) with
  | nil => rfl
  | cons i l ih => simpa using ih
end GlobalTheory.FormalOrigin
