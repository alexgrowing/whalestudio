import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_cocycle_of_map_to_X_one :
    ∀ (C : Shv ℤ) (I : Cx ℤ) (ψ : C ⟶ I.X 1), ψ ≫ I.d 1 2 = 0 →
      ∃ w : Cocycle (sgl C) I 1, sglι C ≫ w.1.v 0 1 (zero_add 1) = ψ := by
  intro C I ψ hψ
  refine ⟨Cocycle.fromSingleMk ψ (zero_add 1) 2 (by norm_num) hψ, ?_⟩
  rw [Cocycle.fromSingleMk_coe, Cochain.fromSingleMk_v]
  exact (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 C).inv_hom_id_assoc ψ

end GlobalTheory.EtC
