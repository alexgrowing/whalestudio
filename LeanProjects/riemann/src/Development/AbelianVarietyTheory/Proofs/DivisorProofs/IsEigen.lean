import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenDescent

variable {X Y : Scheme.{0}}

def evU {Z : Scheme.{0}} (g : Z ⟶ X) {W : X.Opens} (hg : ∀ z, g z ∈ W) (f : Γ(X, W)ˣ) : Γ(Z, ⊤)ˣ :=
  res (fun z _ => hg z : (⊤ : Z.Opens) ≤ g ⁻¹ᵁ W) (pullU g W f)

def rat (π : X ⟶ Y) {V W : Y.Opens} (f : Γ(X, π ⁻¹ᵁ V)ˣ) (g : Γ(X, π ⁻¹ᵁ W)ˣ) :
    Γ(X, π ⁻¹ᵁ (V ⊓ W))ˣ :=
  res (π.preimage_mono inf_le_left) f * (res (π.preimage_mono inf_le_right) g)⁻¹

def Chart (π : X ⟶ Y) (E : ∀ V : Y.Opens, Γ(X, π ⁻¹ᵁ V)ˣ → Prop) : Type :=
  {p : (V : Y.Opens) × Γ(X, π ⁻¹ᵁ V)ˣ // E p.1 p.2}

open Classical in

def trans (π : X ⟶ Y) (E : ∀ V : Y.Opens, Γ(X, π ⁻¹ᵁ V)ˣ → Prop) (i j : Chart π E) :
    Γ(Y, i.1.1 ⊓ j.1.1)ˣ :=
  if h : ∃ u, pullU π _ u = rat π i.1.2 j.1.2 then h.choose else 1

def eigenLB (π : X ⟶ Y) (E : ∀ V : Y.Opens, Γ(X, π ⁻¹ᵁ V)ˣ → Prop) : LB Y :=
  ⟨Chart π E, fun i => i.1.1, trans π E⟩

theorem le_pre {X₂ Z : Scheme.{0}} {π : X ⟶ Y} {ρ : X₂ ⟶ Z} {φ : Z ⟶ Y} {ψ : X₂ ⟶ X}
    (e : ψ ≫ π = ρ ≫ φ) (V : Y.Opens) : ρ ⁻¹ᵁ (φ ⁻¹ᵁ V) ≤ ψ ⁻¹ᵁ (π ⁻¹ᵁ V) := by
  intro x hx
  change (ψ ≫ π).base x ∈ V
  rw [e]
  exact hx

def addRat {X₂ Z : Scheme.{0}} {π : X ⟶ Y} {ρ : X₂ ⟶ Z} {φ₁ φ₂ φ₃ : Z ⟶ Y} {ψ₁ ψ₂ ψ₃ : X₂ ⟶ X}
    (e₁ : ψ₁ ≫ π = ρ ≫ φ₁) (e₂ : ψ₂ ≫ π = ρ ≫ φ₂) (e₃ : ψ₃ ≫ π = ρ ≫ φ₃) {V₁ V₂ V₃ : Y.Opens}
    (f₁ : Γ(X, π ⁻¹ᵁ V₁)ˣ) (f₂ : Γ(X, π ⁻¹ᵁ V₂)ˣ) (f₃ : Γ(X, π ⁻¹ᵁ V₃)ˣ) :
    Γ(X₂, ρ ⁻¹ᵁ (φ₁ ⁻¹ᵁ V₁ ⊓ (φ₂ ⁻¹ᵁ V₂ ⊓ φ₃ ⁻¹ᵁ V₃)))ˣ :=
  res ((ρ.preimage_mono inf_le_left).trans (le_pre e₁ V₁)) (pullU ψ₁ _ f₁) *
    (res ((ρ.preimage_mono (inf_le_right.trans inf_le_left)).trans (le_pre e₂ V₂)) (pullU ψ₂ _ f₂) *
      res ((ρ.preimage_mono (inf_le_right.trans inf_le_right)).trans (le_pre e₃ V₃)) (pullU ψ₃ _ f₃))⁻¹

section Eigen

variable {K : Type} [Field K] {A A' T : Over (Sp K)} [GrpObj A] [GrpObj A']

def IsEigen (q : A ⟶ A') (χ : ∀ (Y : Over (Sp K)) (n : Y ⟶ A), n ≫ q = 1 → (Y ⟶ T) → (Γ(Y.left, ⊤))ˣ)
    {V : (A' ⊗ T).left.Opens} (f : Γ((A ⊗ T).left, (q ▷ T).left ⁻¹ᵁ V)ˣ) : Prop :=
  ∀ (Y : Over (Sp K)) (a n : Y ⟶ A) (h : n ≫ q = 1) (t : Y ⟶ T)
    (ha : ∀ z, (lift a t).left z ∈ (q ▷ T).left ⁻¹ᵁ V) (hb : ∀ z, (lift (a * n) t).left z ∈ (q ▷ T).left ⁻¹ᵁ V),
    evU (lift (a * n) t).left hb f = χ Y n h t * evU (lift a t).left ha f

end Eigen

end GlobalTheory.EigenDescent
