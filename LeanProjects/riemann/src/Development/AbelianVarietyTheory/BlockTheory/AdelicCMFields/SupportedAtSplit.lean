import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct

section Notions

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def evalAt (v : HeightOneSpectrum (𝓞 F)) : FiniteAdeleRing (𝓞 F) F →ₐ[F] v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable (E) in

def loc (v : HeightOneSpectrum (𝓞 F)) : RA F E →ₐ[F] v.adicCompletion F ⊗[F] E :=
  Algebra.TensorProduct.map (evalAt v) (AlgHom.id F E)

variable (F) in

def ratM {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) (RA F E) :=
  γ.map fun e => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e

def IsUnitaryA (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (g : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∀ x y : Fin n → RA F E, hermA c G (g.mulVec x) (g.mulVec y) = hermA c G x y

variable (E) in

def IsSplitPlace (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ w w' : Ideal (𝓞 E), w ≠ w' ∧ w.IsPrime ∧ w'.IsPrime ∧
    w.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal ∧ w'.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal

def SupportedAtSplit (N : ℕ) {n : ℕ} (h : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∃ T : Finset (HeightOneSpectrum (𝓞 F)),
    (∀ v ∈ T, IsSplitPlace E v ∧ (N : 𝓞 F) ∉ v.asIdeal) ∧ ∀ v ∉ T, h.map (loc E v) = 1

def Stabilises {n : ℕ} (L : Set (Fin n → E)) (k : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  k.mulVec '' (hat F L : Set (Fin n → RA F E)) = hat F L

def CongOneAt (N D : ℕ) {n : ℕ} (L : Set (Fin n → E)) (k : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal →
    ∀ x ∈ hat F L, ∃ y ∈ hat F L, ∀ i, loc E v (k.mulVec x i - x i) = loc E v ((D • y) i)

def InLevel (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (N D : ℕ)
    (k : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  IsUnitaryA c G k ∧ Stabilises L k ∧ CongOneAt N D L k

def HasSplitRepresentatives (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (L : Set (Fin n → E)) (N D : ℕ) : Prop :=
  ∀ g : Matrix (Fin n) (Fin n) (RA F E), IsUnitaryA c G g →
    ∃ (γ : Matrix (Fin n) (Fin n) E) (h k : Matrix (Fin n) (Fin n) (RA F E)),
      IsUnitaryA c G (ratM F γ) ∧ (IsUnitaryA c G h ∧ SupportedAtSplit N h) ∧ InLevel c G L N D k ∧
        g = ratM F γ * h * k

end Notions

def SplitRepresentatives : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 →
    ∀ (n : ℕ), 2 ≤ n → ∀ G : Matrix (Fin n) (Fin n) E, (∀ a b, G b a = c (G a b)) → G.det ≠ 0 →
    ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ →
    ∀ N D : ℕ, N ≠ 0 → D ≠ 0 → HasSplitRepresentatives c G (L : Set (Fin n → E)) N D

def SplitRepresentativesCM : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E]
    (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 →
    ∀ (n : ℕ), 2 ≤ n → ∀ G : Matrix (Fin n) (Fin n) E, (∀ a b, G b a = c (G a b)) → G.det ≠ 0 →
    ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ →
    ∀ N D : ℕ, N ≠ 0 → D ≠ 0 → HasSplitRepresentatives c G (L : Set (Fin n → E)) N D

theorem SplitRepresentatives.cm (H : SplitRepresentatives) : SplitRepresentativesCM :=
  fun F E _ _ _ _ _ _ _ => H F E

section Basic₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
