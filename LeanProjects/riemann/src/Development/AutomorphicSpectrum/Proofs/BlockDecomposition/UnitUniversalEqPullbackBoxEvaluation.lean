import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem con_evF_eq_evL [Finite (Fin (0 + 1) ⥤ C)] (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (T : C)
    (u : ∀ a : Fin (0 + 1) ⥤ C, F.obj (a.obj (Fin.last 0)) ⊗[R] F.obj T) :
    con (fun a : Fin (0 + 1) ⥤ C ↦ F.obj (a.obj (Fin.last 0))) (F.obj T) (evF F T₀ ε) u =
      evL F T₀ T ε (u ((Functor.const (Fin (0 + 1))).obj T₀)) := by
  refine pure_induction (fun a : Fin (0 + 1) ⥤ C ↦ F.obj (a.obj (Fin.last 0))) (F.obj T)
    (P := fun u ↦ con (fun a : Fin (0 + 1) ⥤ C ↦ F.obj (a.obj (Fin.last 0))) (F.obj T) (evF F T₀ ε) u =
      evL F T₀ T ε (u ((Functor.const (Fin (0 + 1))).obj T₀))) ?_ ?_ ?_ u
  · rw [map_zero]
    exact (map_zero (evL F T₀ T ε)).symm
  · intro f m
    rw [con_pure]
    show evF F T₀ ε f • m = evL F T₀ T ε (f ((Functor.const (Fin (0 + 1))).obj T₀) ⊗ₜ m)
    simp only [evL, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.id_apply,
      Algebra.smul_def]
    rfl
  · intro u v hu hv
    rw [map_add, hu, hv]
    exact (map_add (evL F T₀ T ε) _ _).symm

theorem tmap_mp_id {T T' : C} (t : F.obj T ⊗[R] F.obj T') :
    Algebra.TensorProduct.map (mp F (𝟙 T)) (mp F (𝟙 T')) t = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul x y => simp only [Algebra.TensorProduct.map_tmul, mp_id]
  | add x y hx hy => rw [map_add, hx, hy]

theorem UU_evF [Finite (Fin (0 + 1) ⥤ C)] (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (n : ℕ) (w : Cn (box F) n) :
    UU F (evF F T₀ ε) n w = pulln (boxE F T₀ ε) n w := by
  funext b
  have h1 : UU F (evF F T₀ ε) n w b = con (fun a : Fin (0 + 1) ⥤ C ↦ F.obj (a.obj (Fin.last 0)))
      (F.obj (b.obj (Fin.last n))) (evF F T₀ ε) (fun a ↦ S0 F n w a b) := rfl
  have hb : b.map (homOfLE (Fin.le_last (Fin.last n))) = 𝟙 _ := by
    rw [show homOfLE (Fin.le_last (Fin.last n)) = 𝟙 _ from Subsingleton.elim _ _, b.map_id]
  have h2 : S0 F n w ((Functor.const (Fin (0 + 1))).obj T₀) b = w (b ⋙ CategoryTheory.Prod.sectR T₀ C) := by
    show Algebra.TensorProduct.map (mp F (𝟙 T₀)) (mp F (b.map (homOfLE (Fin.le_last (Fin.last n)))))
      (w (b ⋙ CategoryTheory.Prod.sectR T₀ C)) = _
    rw [hb]
    exact tmap_mp_id F _
  rw [h1, con_evF_eq_evL, pulln_apply, h2]
  rfl

end GlobalTheory.CompanionTheory.HopfC
