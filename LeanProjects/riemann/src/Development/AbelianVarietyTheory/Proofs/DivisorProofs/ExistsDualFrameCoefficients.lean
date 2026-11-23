import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionChart
open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false

namespace GlobalTheory.VB

open GlobalTheory.Twist (resM resM_self)

theorem IsVB.exists_frame_coord_eq {X : Scheme.{0}} {F : X.Modules} {n : ℕ} (hF : IsVB F n) {V : X.Opens}
    {ι : Type} [Fintype ι] {e : ι → Γ(VB.dual F, V)} (he : IsFrame e) :
    ∃ (e' : ι → Γ(F, V)) (he' : IsFrame e'), ∀ l, he'.coord l = e l := by
  classical
  have := hF.isIso_toBidual_of_local_frames
  have he' : IsFrame fun j => (inv (cartierDualToBidual F)).app V (he.coord j) := he.dual.map_iso _
  refine ⟨_, he', fun l => ?_⟩
  have key (j : ι) : he'.dual.coord j = he.coord j := by
    rw [← he'.toBidual_app j]
    change (inv (cartierDualToBidual F) ≫ cartierDualToBidual F).app V (he.coord j) = _
    rw [IsIso.inv_hom_id]
    rfl
  refine (he.basis le_rfl).repr.injective (Finsupp.ext fun j => ?_)
  have h₁ := he'.dual.dualApp_coord_frame j l le_rfl
  have h₂ := he.dualApp_coord_frame j l le_rfl
  rw [key, resM_self] at h₁
  rw [resM_self] at h₂
  exact h₁.trans h₂.symm

end GlobalTheory.VB

namespace GlobalTheory.ChainPts

theorem exists_frame_coef_dual_eq : ∀ (X : Scheme.{0}) (F : X.Modules) (n r : ℕ), GlobalTheory.VB.IsVB F n → ∀ (V : X.Opens) (e : Fin r → Γ(GlobalTheory.VB.dual F, V)) (he : GlobalTheory.VB.IsFrame e), ∃ (e' : Fin r → Γ(F, V)) (he' : GlobalTheory.VB.IsFrame e'), ∀ (V' : X.Opens) (s : Fin r → Γ(F, V')) (hs : GlobalTheory.VB.IsFrame s) (l i : Fin r), GlobalTheory.ChainPts.coef true he hs.dual l i = GlobalTheory.ChainPts.coef false he' hs l i := by
  intro X F n r hF V e he
  obtain ⟨e', he', h⟩ := hF.exists_frame_coord_eq he
  refine ⟨e', he', fun V' s hs l i => ?_⟩
  refine (hs.dual_basis_repr inf_le_right _ i).trans ?_
  rw [GlobalTheory.VB.dualApp_res, ← h l]
  rfl

end GlobalTheory.ChainPts
