import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]

private theorem cochainReindex_apply_const_obj (F : C ⥤ CommAlgCat.{0} R) {n m : ℕ}
    (e : Fin (n + 1) →o Fin (m + 1)) (x : MainStatements.Hodge.Cn F n) (T₀ : C) :
    GlobalTheory.CompanionTheory.HopfC.pr F e x ((Functor.const (Fin (m + 1))).obj T₀) =
      x ((Functor.const (Fin (n + 1))).obj T₀) := by
  first
  | exact GlobalTheory.CatCoh.mp_id F T₀ _
  | exact (GlobalTheory.CatCoh.mp_id F T₀ (x ((Functor.const (Fin (n + 1))).obj T₀)) : _)
  | (simp only [GlobalTheory.CompanionTheory.HopfC.pr]; exact GlobalTheory.CatCoh.mp_id F T₀ _)

theorem cocycle_const (F : C ⥤ CommAlgCat.{0} R) (T₀ : C) (x : Cn F 1) (hx : dn F 1 x = 0) :
    x ((Functor.const (Fin (1 + 1))).obj T₀) = 0 := by
  have h : MainStatements.Hodge.dn F 1 x ((Functor.const (Fin (1 + 1 + 1))).obj T₀) = 0 := by
    rw [hx]; rfl
  rw [GlobalTheory.CompanionTheory.HopfC.dn_eq] at h
  first
  | rw [Fin.sum_univ_three] at h
  | simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at h
  simp only [Pi.add_apply, Pi.smul_apply, cochainReindex_apply_const_obj] at h
  first
  | simpa using h
  | (norm_num at h; exact h)

theorem evL_tmul_one (F : C ⥤ CommAlgCat.{0} R) (T₀ T : C) (ε : F.obj T₀ →ₐ[R] R) (a : F.obj T₀) :
    evL F T₀ T ε (a ⊗ₜ[R] 1) = algebraMap R (F.obj T) (ε a) := by
  first
  | simp [MainStatements.Hodge.evL, Algebra.ofId_apply]
  | (rw [MainStatements.Hodge.evL, Algebra.TensorProduct.lift_tmul]; simp [Algebra.ofId_apply])

theorem evL_one_tmul (F : C ⥤ CommAlgCat.{0} R) (T₀ T : C) (ε : F.obj T₀ →ₐ[R] R) (b : F.obj T) :
    evL F T₀ T ε (1 ⊗ₜ[R] b) = b := by
  first
  | simp [MainStatements.Hodge.evL, Algebra.ofId_apply]
  | (rw [MainStatements.Hodge.evL, Algebra.TensorProduct.lift_tmul]; simp [Algebra.ofId_apply])

theorem boxE_pull_boxL_boxR (F : C ⥤ CommAlgCat.{0} R) (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (x : Cn F 1)
    (hx : dn F 1 x = 0) :
    pulln (boxE F T₀ ε) 1 (pulln (boxL F) 1 x) = 0 ∧ pulln (boxE F T₀ ε) 1 (pulln (boxR F) 1 x) = x := by
  have h0 := GlobalTheory.CompanionTheory.HopfC.cocycle_const F T₀ x hx
  refine ⟨?_, ?_⟩
  · funext c
    calc _ = MainStatements.Hodge.evL F T₀ (c.obj (Fin.last 1)) ε
          (x ((Functor.const (Fin (1 + 1))).obj T₀) ⊗ₜ[R] 1) := rfl
      _ = algebraMap R _ (ε (x ((Functor.const (Fin (1 + 1))).obj T₀))) :=
          GlobalTheory.CompanionTheory.HopfC.evL_tmul_one F T₀ _ ε _
      _ = 0 := by rw [h0, map_zero, map_zero]
  · funext c
    calc _ = MainStatements.Hodge.evL F T₀ (c.obj (Fin.last 1)) ε (1 ⊗ₜ[R] x c) := rfl
      _ = x c := GlobalTheory.CompanionTheory.HopfC.evL_one_tmul F T₀ _ ε _

end GlobalTheory.CompanionTheory.HopfC
