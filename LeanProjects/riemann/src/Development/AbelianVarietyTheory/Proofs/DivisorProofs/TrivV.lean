import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

def trivV (N : ℕ) (E : Spc) : E ⟶ ofCat (glCat N) where
  app n :=
    { app := fun U => TypeCat.ofHom fun _ =>
        (show Fin (n.unop.len + 1) ⥤ (glCat N).obj (Scheme.Γ.obj U) from
          (CategoryTheory.Functor.const _).obj (SingleObj.star (GL (Fin N) (Scheme.Γ.obj U))))
      naturality := fun U U' f => by
        ext x
        exact CategoryTheory.Functor.hext (fun _ => rfl)
          (fun _ _ _ => heq_of_eq (map_one (Matrix.GeneralLinearGroup.map _)).symm) }
  naturality n m f := by
    ext U x
    exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq rfl)

end GlobalTheory.EtC

end
