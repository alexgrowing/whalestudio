import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.PositiveSignKForm

open GlobalTheory.CM

section Form

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def kForm (D : Datum H) (ε : ℤˣ) (x y : D.La) : OK H :=
  (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : OK H) + (((ε : ℤ) * D.EF x y : ℤ) : OK H) * wK H

def IsPosSign (D : Datum H) (ε : ℤˣ) : Prop := ∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x

theorem IsPosSign.unique {D : Datum H} [Nontrivial D.La] {ε ε' : ℤˣ} (h : IsPosSign D ε) (h' : IsPosSign D ε') :
    ε = ε' := by
  obtain ⟨x, hx⟩ := exists_ne (0 : D.La)
  have h₁ := h x hx
  have h₂ := h' x hx
  rcases Int.units_eq_one_or ε with rfl | rfl <;> rcases Int.units_eq_one_or ε' with rfl | rfl <;>
    first | rfl | (simp at h₁ h₂; omega)

end Form

def TensorObject : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H), 1 ≤ D.p + D.q →
  ∀ (M : Type) [Field M] [NumberField M] (ω : 𝓞 M) (C : Ell H (𝓞 M) ω) (σ : M →+* ℂ),
    (D.q = 0 ∧ σ ((2 * ω - 1 : 𝓞 M) : M) = H.rt0) ∨ (D.p = 0 ∧ σ ((2 * ω - 1 : 𝓞 M) : M) = -H.rt0) →
    C.IsPrincipalAt (σ.comp (algebraMap (𝓞 M) M)) →
    ∃ (ε : ℤˣ) (T : PAT H (Sp (𝓞 M))), IsPosSign D ε ∧ Nonempty (IsTen C D (kForm D ε) T) ∧
      ∃ (K₁ : IntermediateField ℚ ℂ) (hK : KA l ≤ K₁) (jM : M →+* K₁)
        (o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion hK).toRingHom)),
        FiniteDimensional ℚ K₁ ∧ (algebraMap K₁ ℂ).comp jM = σ ∧
        Nonempty (SABMap o.t T.t (spMap (jM.comp (algebraMap (𝓞 M) M))))

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def TiedToLattices {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} {hP : IsPeriod D ty Pe}
    {p q : ℕ} (Z : CMLat hP p q) {K₁ : Type} [Field K₁] [NumberField K₁] {ρ : 𝓞 K₁} {σ₁ : K₁ →+* ℂ}
    (X : CMObj H K₁ ρ σ₁ p q)
    (eB : (Fin g → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K₁) K₁))) ⟶ X.B.t.G)) : Prop :=
  X.hh = Z.hh ∧ IsExp X.B (σ₁.comp (algebraMap (𝓞 K₁) K₁)) D ty Pe eB ∧
  ∃ (g₁ : Bool → ℕ) (ty₁ : ∀ b, Fin (g₁ b) → (E →+* ℂ)) (Pe₁ : ∀ b, (Z.D₁ b).La →+ (Fin (g₁ b) → ℂ))
    (e₁ : ∀ b, (Fin (g₁ b) → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K₁) K₁))) ⟶ (X.A b).t.G)),
    (∀ b, IsTypeFn H (Z.D₁ b).p (Z.D₁ b).q (ty₁ b) ∧
      IsExp (X.A b) (σ₁.comp (algebraMap (𝓞 K₁) K₁)) (Z.D₁ b) (ty₁ b) (Pe₁ b) (e₁ b)) ∧
    ∀ j : Fin p ⊕ Fin q, ∃ F : (Fin (g₁ j.isLeft) → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      (∀ a, F (Pe₁ j.isLeft a) = Pe (Z.f j a)) ∧ ∀ z, e₁ j.isLeft z ≫ X.φ j = eB (F z)

end Comparison₂

def CMObject : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l),
    1 ≤ D.p + D.q →
  ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty →
  ∀ (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (FU.Di i) ty Pe) (Z : CMLat hP D.p D.q) (K' : IntermediateField ℚ ℂ), FiniteDimensional ℚ K' →
    ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hK : KA l ≤ K₁) (ρ : 𝓞 K₁)
      (X : CMObj H K₁ ρ (algebraMap K₁ ℂ) D.p D.q) (y : Sp K₁ ⟶ Xo.X) (t : SAB H (Sp K₁))
      (m : SABMap t Xo.univ.t y) (n : SABMap t X.B.t (spMap (algebraMap (𝓞 K₁) K₁)))
      (eB : (Fin g → ℂ) → (Over.mk (spMap ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁))) ⟶ X.B.t.G)),
      K' ≤ K₁ ∧ algebraMap K₁ ℂ (ρ : K₁) = H.rt0 ∧
      y ≫ Xo.s = spMap (IntermediateField.inclusion hK).toRingHom ∧
      spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe ∧
      (∀ z, ∃ x : Sp ℂ ⟶ t.G.left, x ≫ n.φ = (eB z).left ∧ x ≫ m.φ = (FU.ex i Pe z).left) ∧
      TiedToLattices Z X eB

def Existence : Prop := TensorObject ∧ CMObject

end GlobalTheory.IndefiniteRowSideFullHecke.PositiveSignKForm
end
