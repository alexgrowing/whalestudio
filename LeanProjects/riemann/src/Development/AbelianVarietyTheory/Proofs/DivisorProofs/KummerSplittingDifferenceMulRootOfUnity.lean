import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSecOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfUnityEtaleLocallyPowPrimitiveRootStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

theorem unitSec_mul_kd {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v :=
  map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom
    (ULift.up (Additive.ofMul u) : (Scheme.Γ ⋙ unitsF).obj (op U)) (ULift.up (Additive.ofMul v))

theorem unitSec_res_kd {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  unfold unitSec ofRings.sec
  have := congrArg (fun f => f.hom (ULift.up (Additive.ofMul u) : (Scheme.Γ ⋙ unitsF).obj (op U)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op)
  exact this.symm

theorem Sec.res_map_kd {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := congrArg (fun f => f.hom x) (φ.hom.naturality g.op)
  exact this.symm

theorem Sec.map_add_kd {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ x y

theorem Sec.res_sub_kd {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x - y) = Sec.res g x - Sec.res g y := map_sub _ x y

theorem Prim.pow_eq_one_kd {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hg
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

def kumDiff (q : ℕ) (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0) (U : Scheme.{0})
    (v : (Γ(U, ⊤))ˣ) : Sec ((res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0) U :=
  Sec.map φ (unitSec v) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U v)

theorem kumDiff_res (q : ℕ) (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0)
    {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) (v : (Γ(U, ⊤))ˣ) :
    Sec.res g (kumDiff q φ U v) = kumDiff q φ V (Units.map g.appTop.hom.toMonoidHom v) := by
  unfold kumDiff
  rw [Sec.res_sub_kd, Sec.res_map_kd, unitSec_res_kd, (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).nat g 0,
    (kumT_spec q).1 V U g v hq]

theorem kumDiff_mul_root (q : ℕ) (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm)
    (hκ : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
      Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u)
    (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0)
    (hφ : κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)))
    {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) (z w : (Γ(V, ⊤))ˣ) (hz : (z : Γ(V, ⊤)) = ζ.1) :
    kumDiff q φ V (z * w) = kumDiff q φ V w := by
  unfold kumDiff
  have h1 : Sec.map φ (unitSec z) =
      Sec.map (resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)))
        (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) V from twGen 1 ζ) := by
    rw [← hκ V ζ z hz, ← hφ]; rfl
  have h2 := (kumT_spec q).2 V ζ w (z * w) (by rw [Units.val_mul, hz])
  have h3 := restrMap_spec (Int.castRingHom (ZMod q)) (tw q 1) V (twGen 1 ζ)
  rw [unitSec_mul_kd, Sec.map_add_kd, h2, map_add, h1]
  unfold resGen
  rw [h3]
  abel

end GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem kumDiff_pow_root (q : ℕ) (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm)
    (hκ : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
      Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u)
    (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0)
    (hφ : κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)))
    {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) (z : (Γ(V, ⊤))ˣ) (hz : (z : Γ(V, ⊤)) = ζ.1) (a : ℕ) (w : (Γ(V, ⊤))ˣ) :
    kumDiff q φ V (z ^ a * w) = kumDiff q φ V w := by
  induction a with
  | zero => rw [pow_zero, one_mul]
  | succ a ih => rw [pow_succ', mul_assoc, kumDiff_mul_root q κ hκ φ hφ ζ z _ hz, ih]

theorem kumDiff_mul_rootOfUnity : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm),
    (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
      Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) →
    ∀ φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0,
      κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) →
    ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ (v ω : (Γ(U, ⊤))ˣ), ω ^ q = 1 →
      Sec.map φ (unitSec (ω * v)) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U (ω * v)) =
        Sec.map φ (unitSec v) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U v) := by
  intro q _ κ hκ φ hφ U hq v ω hω
  change kumDiff q φ U (ω * v) = kumDiff q φ U v
  obtain ⟨S, hS, hP⟩ := GlobalTheory.T.rootOfUnity_etaleLocally_pow_primitiveRoot q U hq ω hω
  refine Sheaf.isSeparated _ U S hS _ _ ?_
  intro V g hg
  obtain ⟨ζ, a, ha⟩ := hP V g hg
  change Sec.res g _ = Sec.res g _
  rw [kumDiff_res q φ g hq, kumDiff_res q φ g hq, map_mul]
  have hz := Units.val_ofPowEqOne ζ.1 q ζ.pow_eq_one_kd (NeZero.ne q)
  have e : Units.map g.appTop.hom.toMonoidHom ω = Units.ofPowEqOne ζ.1 q ζ.pow_eq_one_kd (NeZero.ne q) ^ a :=
    Units.ext (by rw [ha, Units.val_pow_eq_pow_val, hz])
  rw [e]
  exact kumDiff_pow_root q κ hκ φ hφ ζ _ hz a _

end GlobalTheory.EtC

end
