import Mathlib

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.NormalizationOpenImmersion

theorem isOpenImmersion_toNormalization {V P X : Scheme.{0}} (c : V ⟶ P) (p : P ⟶ X) [IsSeparated p]
    (j : V ⟶ X) [IsOpenImmersion j] [inst : QuasiCompact c] [inst_1 : QuasiSeparated c]
    (h : c ≫ p = j) : IsOpenImmersion c.toNormalization := by
  have : IsImmersion (c ≫ p) := h ▸ inferInstance
  have : IsImmersion c := IsImmersion.of_comp c p
  infer_instance

theorem main : ∀ {V P X : AlgebraicGeometry.Scheme.{0}} (c : V ⟶ P) (p : P ⟶ X) [IsSeparated p]
    (j : V ⟶ X) [IsOpenImmersion j] [inst : QuasiCompact c] [inst_1 : QuasiSeparated c]
    (h : c ≫ p = j), IsOpenImmersion c.toNormalization :=
  fun c p _ j _ _ _ h => isOpenImmersion_toNormalization c p j h

end GlobalTheory.NormalizationOpenImmersion
