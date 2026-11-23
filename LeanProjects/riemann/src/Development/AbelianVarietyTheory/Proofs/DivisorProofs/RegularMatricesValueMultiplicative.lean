import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnEquivApply

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat GlobalTheory.WholeFlag.Glue GlobalTheory.ConstLat.CramerFrame
open scoped Classical

namespace GlobalTheory.ConstLat.CramerValues

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z]

theorem exists_germ_matrix {x : Z} {n m : ℕ} (P : Matrix (Fin n) (Fin m) Z.functionField)
    (hP : ∀ a b, RegAt x (P a b)) :
    ∃ A : Matrix (Fin n) (Fin m) (Z.presheaf.stalk x), P = A.map (algebraMap _ Z.functionField) := by
  choose A hA using hP
  exact ⟨Matrix.of A, by ext a b; exact (hA a b).symm⟩

theorem map_valAt_germ (z : Sp K ⟶ Z) {n m : ℕ} (A : Matrix (Fin n) (Fin m) (Z.presheaf.stalk (below z))) :
    (A.map (algebraMap _ Z.functionField)).map (valAt z) = A.map (Scheme.stalkClosedPointTo z).hom := by
  ext a b
  exact Base.valAt_stalk z (A a b)

theorem minorAt_map_ringHom {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n g : ℕ}
    (A : Matrix (Fin n) (Fin g) R) (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin n) :
    minorAt (A.map f) k hk τ = f (minorAt A k hk τ) := by
  unfold minorAt
  rw [RingHom.map_det]
  rfl

theorem values_regular : ∀ {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (z : Sp K ⟶ Z), (∀ {n m l : ℕ} (P : Matrix (Fin n) (Fin m) Z.functionField) (Q : Matrix (Fin m) (Fin l) Z.functionField), (∀ a b, RegAt (below z) (P a b)) → (∀ a b, RegAt (below z) (Q a b)) → (∀ a b, RegAt (below z) ((P * Q) a b)) ∧ (P * Q).map (valAt z) = P.map (valAt z) * Q.map (valAt z)) ∧ (∀ {n g : ℕ} (P : Matrix (Fin n) (Fin g) Z.functionField), (∀ a b, RegAt (below z) (P a b)) → ∀ (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin n), RegAt (below z) (minorAt P k hk τ) ∧ valAt z (minorAt P k hk τ) = minorAt (P.map (valAt z)) k hk τ) ∧ ∀ (a b : Z.functionField), RegAt (below z) a → UnitAt (below z) b → RegAt (below z) (a / b) ∧ valAt z (a / b) = valAt z a / valAt z b := by
  intro K _ Z _ z
  refine ⟨fun P Q hP hQ => ?_, fun P hP k hk τ => ?_, fun a b ha hb => ?_⟩
  · obtain ⟨A, rfl⟩ := exists_germ_matrix P hP
    obtain ⟨B, rfl⟩ := exists_germ_matrix Q hQ
    rw [← Matrix.map_mul]
    refine ⟨fun a b => ⟨_, rfl⟩, ?_⟩
    rw [map_valAt_germ, map_valAt_germ, map_valAt_germ]
    exact Matrix.map_mul
  · obtain ⟨A, rfl⟩ := exists_germ_matrix P hP
    rw [minorAt_map_ringHom, map_valAt_germ, Base.valAt_stalk]
    exact ⟨⟨_, rfl⟩, (minorAt_map_ringHom _ A k hk τ).symm⟩
  · obtain ⟨a, rfl⟩ := ha
    obtain ⟨_, ⟨u, rfl⟩, rfl⟩ := hb
    have e {S : Type} [Field S] (ψ : Z.presheaf.stalk (below z) →+* S) :
        ψ a / ψ u = ψ (a * (u⁻¹ : _ˣ)) := by
      rw [map_mul, map_units_inv, div_eq_mul_inv]
    rw [e, Base.valAt_stalk, Base.valAt_stalk, Base.valAt_stalk]
    exact ⟨⟨_, rfl⟩, (e _).symm⟩

end GlobalTheory.ConstLat.CramerValues

end
