import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.BdDim

def TrLe (K : Type) [Field K] (n : ℕ) : Prop := Algebra.trdeg (⊥ : Subfield K) K ≤ n

theorem TrLe.mono {K : Type} [Field K] {n m : ℕ} (h : TrLe K n) (hnm : n ≤ m) : TrLe K m :=
  le_trans h (by exact_mod_cast hnm)

theorem TrLe.of_ringHom {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (h : TrLe L n) : TrLe K n := by
  have hb : ∀ x : (⊥ : Subfield K), f x ∈ (⊥ : Subfield L) := fun x =>
    (show (⊥ : Subfield K) ≤ (⊥ : Subfield L).comap f from bot_le) x.2
  let e : (⊥ : Subfield K) →+* (⊥ : Subfield L) := (f.comp (Subfield.subtype _)).codRestrict _ hb
  have he : Function.Surjective e := fun y => by
    have : (⊥ : Subfield L) ≤ (⊥ : Subfield K).map f := bot_le
    obtain ⟨x, hx, hxy⟩ := this y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (⊥ : Subfield K) K
  refine le_trans ?_ h
  rw [← hs.cardinalMk_eq_trdeg]
  have := hs.1.ringHom_of_comp_eq e f he f.injective (RingHom.ext fun _ => rfl)
  exact this.cardinalMk_le_trdeg

example : TrLe ℚ 0 := by
  have : Algebra.IsAlgebraic (⊥ : Subfield ℚ) ℚ := ⟨fun x => isAlgebraic_algebraMap (⟨x, by simpa using SubfieldClass.ratCast_mem (⊥ : Subfield ℚ) x⟩ : (⊥ : Subfield ℚ))⟩
  simp [TrLe, trdeg_eq_zero]

section Fibres

variable {T X Y Z : Scheme.{0}}

def SameFibre (G : Over X) [GrpObj G] (x : T ⟶ X) (G' : Over Y) [GrpObj G'] (y : T ⟶ Y) : Prop :=
  ∃ (A : Over T) (_ : GrpObj A) (φ : A.left ⟶ G.left) (ψ : A.left ⟶ G'.left),
    IsGrpPullback A G x φ ∧ IsGrpPullback A G' y ψ

def IsAbPart {k : Type} [Field k] (G : Over X) [GrpObj G] (x : Sp k ⟶ X) (B : Over Y) [GrpObj B] (y : Sp k ⟶ Y) : Prop :=
  ∃ (A : Over (Sp k)) (_ : GrpObj A) (φ : A.left ⟶ G.left) (t : TorusExtension A) (β : t.B.left ⟶ B.left),
    IsGrpPullback A G x φ ∧ @IsGrpPullback _ _ t.B t.grpB B _ y β

theorem SameFibre.refl (G : Over X) [GrpObj G] (x : T ⟶ X) : SameFibre G x G x :=
  ⟨_, _, _, _, isGrpPullback_pullback G x, isGrpPullback_pullback G x⟩

theorem IsAbPart.trans {k : Type} [Field k] {G : Over X} [GrpObj G] {x : Sp k ⟶ X} {B : Over Y} [GrpObj B] {y : Sp k ⟶ Y}
    {B' : Over Z} [GrpObj B'] {z : Sp k ⟶ Z} (h : IsAbPart G x B y) (h' : SameFibre B y B' z) : IsAbPart G x B' z := by
  obtain ⟨A, _, φ, t, β, h₁, h₂⟩ := h
  obtain ⟨C, _, ψ, ψ', h₃, h₄⟩ := h'
  letI := t.grpB
  obtain ⟨e, he, -⟩ := grpPullback_iso h₂ h₃
  exact ⟨A, _, φ, t, _, h₁, ((isGrpPullback_of_iso e).comp h₄).congr (Category.id_comp _) rfl⟩

theorem IsAbPart.comp {k : Type} [Field k] {G : Over X} [GrpObj G] {x : Sp k ⟶ X} {B : Over Y} [GrpObj B] {y : Sp k ⟶ Y}
    {G' : Over Z} [GrpObj G'] {f : X ⟶ Z} {φ : G.left ⟶ G'.left} (h : IsAbPart G x B y) (h' : IsGrpPullback G G' f φ) :
    IsAbPart G' (x ≫ f) B y := by
  obtain ⟨A, _, φ, t, β, h₁, h₂⟩ := h
  exact ⟨A, _, _, t, β, h₁.comp h', h₂⟩

end Fibres

end GlobalTheory.BdDim

end
