import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualHermitianLatticesTorsionBlocks

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def form (L : LocE F E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  ∑ i, ∑ j, x i * G i j * L.cj (y j)

def IsHermND (L : LocE F E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ i j, G j i = L.cj (G i j)) ∧ IsUnit G.det

def IsLattice (L : LocE F E) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) : Prop :=
  Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤

def IsSelfDual (L : LocE F E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule L.O (Fin n → E)) : Prop :=
  IsLattice L Λ ∧ ∀ y : Fin n → E, y ∈ Λ ↔ ∀ x ∈ Λ, form L G x y ∈ L.O

def IsIsometry (L : LocE F E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Prop :=
  ∀ x y, form L G (g x) (g y) = form L G x y

def HasOrthonormalBasis (L : LocE F E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule L.O (Fin n → E)) : Prop :=
  ∃ b : Module.Basis (Fin n) L.O Λ,
    ∀ i j, form L G (b i : Fin n → E) (b j : Fin n → E) = if i = j then 1 else 0

def SelfDualOneOrbit : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : LocE F E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermND L G →
    (∀ Λ : Submodule L.O (Fin n → E), IsSelfDual L G Λ → HasOrthonormalBasis L G Λ) ∧
    (∀ Λ Λ' : Submodule L.O (Fin n → E), IsSelfDual L G Λ → IsSelfDual L G Λ' →
      ∃ g : (Fin n → E) ≃ₗ[E] (Fin n → E), IsIsometry L G g ∧
        g '' (Λ : Set (Fin n → E)) = (Λ' : Set (Fin n → E)))

theorem cj_mem (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])

theorem isHermND_one (L : LocE F E) (n : ℕ) :
    IsHermND L (1 : Matrix (Fin n) (Fin n) E) := by
  refine ⟨fun i j => ?_, by simp⟩
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualHermitianLatticesTorsionBlocks

end
