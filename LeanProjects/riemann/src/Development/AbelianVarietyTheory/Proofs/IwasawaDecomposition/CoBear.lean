import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

variable {F : Type} [Field F] {ι : Type} {m : ι → ℕ}

def Reps {X Y : GlobalTheory.ProjVar.Var F} (Eb : Fr (ratOf X) m 0) (S : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn)
    (f : Y.X ⟶ X.X) : Prop :=
  (ratOf X).IsHom (ratOf Y) φ f ∧
    (∀ z', ∀ A' ∈ S.S z', ∀ A ∈ Eb.S (f z'), Par 0 ((ratOf Y).O z').toSubring (A' * (A.map φ)⁻¹)) ∧
    ∀ (K : Type) [Field K] (x : Sp K ⟶ X.X), ∀ A ∈ Eb.S (x (IsLocalRing.closedPoint K)), ∀ h : Mat m K,
      Par 0 ⊤ h → ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ Bears S φ A h p

theorem Refines.reps {X Y : GlobalTheory.ProjVar.Var F} {Eb : Fr (ratOf X) m 0} {S : Fr (ratOf Y) m m}
    {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (h : Refines Eb S φ f) : Reps Eb S φ f :=
  ⟨h.hom, h.sub, h.lifts⟩

def CoBear {X Y₁ Y₂ : GlobalTheory.ProjVar.Var F} (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn)
    (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) {K : Type} [Field K] (x : Sp K ⟶ X.X) (p₁ : Sp K ⟶ Y₁.X)
    (p₂ : Sp K ⟶ Y₂.X) : Prop :=
  ∃ A ∈ Eb.S (x (IsLocalRing.closedPoint K)), ∃ h : Mat m K, Par 0 ⊤ h ∧ Bears S₁ φ₁ A h p₁ ∧ Bears S₂ φ₂ A h p₂

end GlobalTheory.FlagBundle
