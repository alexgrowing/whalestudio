import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureType

namespace GlobalTheory.CompRat

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def wC (H : Host E) (s : ℤ × ℤ) : ℂ := s.1 + s.2 * ((1 + H.rt0) / 2)

def wE (H : Host E) (s : ℤ × ℤ) : 𝓞 E := s.1 + s.2 * H.w0

structure Curve (H : Host E) : Type 1 where
  P : Out.PolAV (Sp ℂ)
  g_eq : P.g = 1
  u : HolUnif P.A P.L P.g
  theta : IsThetaUnif u
  c : ℂ
  c_ne : c ≠ 0
  lat : IsQuadLattice u.Λ H.d c

variable {H : Host E}

def Curve.pt (C : Curve H) (z : ℂ) : Sp ℂ ⟶ C.P.A.left := (C.u.ex fun _ => C.c * z).left

def Curve.ActsBy (C : Curve H) (τ : ℂ ≃+* ℂ) (ι : C.P.A.left ⟶ C.P.A.left) (n : ℕ) (s : ℤ × ℤ) : Prop :=
  IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) ι ∧
    ∀ a : ℤ × ℤ, C.pt (wC H s * wC H a / n) ≫ ι = spMap (τ : ℂ →+* ℂ) ≫ C.pt (wC H a / n)

def FixesCurve (H : Host E) (τ : ℂ ≃+* ℂ) (n : ℕ) : Prop := ∃ (C : Curve H) (ι : _), C.ActsBy τ ι n (1, 0)

def CurveOver (H : Host E) (F : IntermediateField ℚ ℂ) (n : ℕ) : Prop :=
  ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ F, τ x = x) → FixesCurve H τ n

def IsSplit {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) : Prop :=
  lat hP H.rt0 ⊔ lat hP (-H.rt0) = ⊤

def SplitLat (D : Datum H) : Prop :=
  ∃ Lp Lm : Submodule (𝓞 E) D.La, Lp ⊔ Lm = ⊤ ∧ (∀ a ∈ Lp, ∀ b ∈ Lm, D.EF a b = 0) ∧
    Module.finrank (𝓞 E) Lp = D.p ∧ Module.finrank (𝓞 E) Lm = D.q ∧
    (∀ a ∈ Lp, a ≠ 0 → 0 < H.rt0.im * D.EF (H.rt • a) a) ∧ ∀ a ∈ Lm, a ≠ 0 → H.rt0.im * D.EF (H.rt • a) a < 0

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

def ConjugationPermutesPeriods (F : FamilyUnif Xo σ ty) (τ : ℂ ≃+* ℂ) (π : Fin F.n → Fin F.n) : Prop :=
  ∀ i P, IsPeriod (F.Di i) ty P →
    ∃ P', IsPeriod (F.Di (π i)) ty P' ∧ spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u (π i) P'

theorem permutes_refl (F : FamilyUnif Xo σ ty) : ConjugationPermutesPeriods F (RingEquiv.refl ℂ) id := fun i P hP =>
  ⟨P, hP, by
    have : spMap ((RingEquiv.refl ℂ : ℂ ≃+* ℂ) : ℂ →+* ℂ) = 𝟙 _ := Spec.map_id (CommRingCat.of ℂ)
    rw [this, Category.id_comp]; rfl⟩

end GlobalTheory.CompRat
