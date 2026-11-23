import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PolDeg.NegPrim
open GlobalTheory.CechPic

variable {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G]

theorem lam_inv_left {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x z : T ⟶ G) :
    lam (cls L hL) x⁻¹ z = - lam (cls L hL) x z := by
  have h := lam_mul_left hL hΘ x⁻¹ x z
  rw [inv_mul_cancel, lam_one_left] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem lam_inv_inv {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x y : T ⟶ G) :
    lam (cls L hL) x⁻¹ y⁻¹ = lam (cls L hL) x y := by
  rw [lam_inv_left hL hΘ, lam_comm, lam_inv_left hL hΘ, lam_comm, neg_neg]

theorem lam_pull_inv (c : Pic G.left) (x y : T ⟶ G) :
    lam (pull (ι[G]).left c) x y = lam c x⁻¹ y⁻¹ := by
  simp only [lam, ← pull_comp, ← Over.comp_left, ← Hom.inv_def, mul_inv, inv_one]

end GlobalTheory.PolDeg.NegPrim

namespace GlobalTheory.PolDeg.NegPrim
open GlobalTheory.CechPic

theorem lam_negPull_sub_isTrivial : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (_ : CubicalStr B M), IsAbelianScheme B → ∃ u : LB.Gen (abelian₂ B (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])), u.IsGen := by
  intro A _ _ _ B _ _ M cub _
  have hΘ : ∃ t : LB.Gen (Theta B M.L), t.IsGen := ⟨cub.t, cub.isGen⟩
  have hN : (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]).IsLB := LB.isLB_linComb M.isLB _ _
  have hΛ : (abelian₂ B (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])).IsLB := LB.isLB_linComb hN _ _
  refine (cls_eq_zero_iff hΛ).1 ?_
  have hc : cls _ hN = pull (ι[B]).left (cls M.L M.isLB) - cls M.L M.isLB := by
    rw [cls_linComb M.isLB, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id, sub_eq_add_neg]
  refine (cls_cube_two hN (fst B B) (snd B B) hΛ).trans ?_
  have e : ∀ (c c' : Pic B.left) (x y : B ⊗ B ⟶ B), lam (c - c') x y = lam c x y - lam c' x y := fun c c' x y => by
    simp only [lam, map_sub]; abel
  rw [hc, e, lam_pull_inv, lam_inv_inv M.isLB hΘ, sub_self]

end GlobalTheory.PolDeg.NegPrim
