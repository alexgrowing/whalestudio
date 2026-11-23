import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

namespace GlobalTheory.LBObs

section Frames

variable {X : Scheme.{0}} {C : Type} [Category.{0} C]

def IsBas (V : C → X.Opens) : Prop :=
  (∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C, x ∈ V t ∧ V t ≤ U) ∧
    ∀ (t₁ t₂ : C) (x : X) (U : X.Opens), x ∈ U → x ∈ V t₁ → x ∈ V t₂ →
      ∃ t₃ : C, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ V t₃ ∧ V t₃ ≤ U

def IsGenOn (L : LB X) (W : X.Opens) (τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ) : Prop :=
  ∀ m m' : L.ι, res (inf_le_left : W ⊓ L.U m ⊓ L.U m' ≤ W ⊓ L.U m) (τ m) =
    res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W ⊓ L.U m ⊓ L.U m' ≤ L.U m ⊓ L.U m') (L.g m m') *
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W ⊓ L.U m ⊓ L.U m' ≤ W ⊓ L.U m') (τ m')

def IsFrame (L : LB X) (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T)
    (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) : Prop :=
  ∃ τ : ∀ (T : C) (m : L.ι), Γ(X, V T ⊓ L.U m)ˣ, (∀ T, IsGenOn L (V T) (τ T)) ∧
    ∀ (T T' : C) (a : T ⟶ T') (m : L.ι), res (inf_le_inf_right (L.U m) (hV a)) (τ T m) =
      res (inf_le_left : V T' ⊓ L.U m ≤ V T') (u T T' a) * τ T' m

def IsCoc (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T)
    (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) : Prop :=
  ∀ ⦃T T' T'' : C⦄ (a : T ⟶ T') (b : T' ⟶ T''), u T T'' (a ≫ b) = res (hV b) (u T T' a) * u T' T'' b

abbrev opOf (G : C ⥤ AffOp X) (T : C) : X.Opens := (G.obj T).unop.1

theorem opOf_le (G : C ⥤ AffOp X) ⦃T T' : C⦄ (a : T ⟶ T') : opOf G T' ≤ opOf G T := leOfHom (G.map a).unop

theorem isCoc_one (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) : IsCoc V hV fun _ _ _ ↦ 1 :=
  fun _ _ _ _ _ ↦ by simp

theorem isBas_opens : IsBas (C := (X.Opens)ᵒᵖ) fun U ↦ U.unop :=
  ⟨fun _ U hx ↦ ⟨Opposite.op U, hx, le_rfl⟩, fun t₁ t₂ _ U hx h₁ h₂ ↦
    ⟨Opposite.op (t₁.unop ⊓ t₂.unop ⊓ U), ⟨(homOfLE (inf_le_left.trans inf_le_left)).op⟩,
      ⟨(homOfLE (inf_le_left.trans inf_le_right)).op⟩, ⟨⟨h₁, h₂⟩, hx⟩, inf_le_right⟩⟩

end Frames

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R₀}

def UCoc (F : C ⥤ CommAlgCat.{0} R₀) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) : Prop :=
  ∀ ⦃T T' T'' : C⦄ (a : T ⟶ T') (b : T' ⟶ T''),
    (u T T'' (a ≫ b) : F.obj T'') = mp F b (u T T' a : F.obj T') * (u T' T'' b : F.obj T'')

def IsObU (L : Pre I π F) (α : Aug I π R₁) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ)
    (c : CatCoh.H2 (ext R₁ F)) : Prop :=
  ∃ (v : ∀ (T T' : C) (_ : T ⟶ T'), (L.B T')ˣ) (σ : ∀ T, R₁ ⊗[R₀] F.obj T →+ L.B T) (z : Z2 (ext R₁ F)),
    (∀ T T' a, L.p T' (v T T' a : L.B T') = (u T T' a : F.obj T')) ∧ (∀ T, α.IsSig (L.p T) (σ T)) ∧ c = H2.mk _ z ∧
      ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), α.KerQ (B₀ := F.obj T'') (z.1 T T' T'' a b) ∧
        L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') = (1 + σ T'' (z.1 T T' T'' a b)) * (v T T'' (a ≫ b) : L.B T'')

variable {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀}

def ObAt (S : Sys I π s₀) (α : Aug I π R₁) (L : LB X₀) (G : C ⥤ AffOp X₀) (d : CatCoh.H2 (ext R₁ (G ⋙ OAff s₀))) : Prop :=
  ∃ u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X₀, opOf G T')ˣ,
    IsFrame L (opOf G) (opOf_le G) u ∧ IsObU ((ofSys S).restrict G) α u d

def IsObL (S : Sys I π s₀) (α : Aug I π R₁) (L : LB X₀) (c : CatCoh.H2 (ext R₁ (OAff s₀))) : Prop :=
  ∃ (C' : Type) (_ : Category.{0} C') (_ : Quiver.IsThin C') (G : C' ⥤ AffOp X₀), IsBas (opOf G) ∧
    ObAt S α L G ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c)

theorem isObU_one (L : Pre I π F) (α : Aug I π R₁) (σ : ∀ T, R₁ ⊗[R₀] F.obj T →+ L.B T)
    (hσ : ∀ T, α.IsSig (L.p T) (σ T)) : IsObU L α (fun _ _ _ ↦ 1) 0 :=
  ⟨fun _ _ _ ↦ 1, σ, 0, fun _ _ _ ↦ by simp, hσ, (map_zero _).symm, fun T T' T'' a b ↦
    ⟨map_zero _, by
      have : (0 : Z2 (ext R₁ F)).1 T T' T'' a b = 0 := rfl
      rw [this, map_zero]; simp⟩⟩

end GlobalTheory.LBObs
