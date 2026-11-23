import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj

namespace GlobalTheory.LineNorm

attribute [local instance] Over.cartesianMonoidalCategory

theorem fromModel_const : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (a : F) (n : ℕ), a ≠ 0 → n ≠ 0 → FromModel Y 0 (fun _ => 1) (fun _ e _ => Real.log (e.w (algebraMap F (AlgebraicClosure F) a)) / n) := by
  intro F _ _ Y a n ha hn
  obtain ⟨M, -⟩ := GlobalTheory.IntModel.exists_model F Y 0
  have ha' : algebraMap F Y.Fn a ≠ 0 := (map_ne_zero _).2 ha
  have hu (x : Y.X) : UnitAt x (algebraMap F Y.Fn a) :=
    (unitAt_iff ha').2 ⟨Y.regAt_algebraMap x a, map_inv₀ (algebraMap F Y.Fn) a ▸ Y.regAt_algebraMap x a⁻¹⟩
  have hL := LB.isLB_pull (LB.isLB_triv M.X) M.j
  refine ⟨M, LB.triv M.X, ⟨n, Nat.pos_of_ne_zero hn⟩, fun _ => Units.mk0 _ ha', LB.isLB_triv M.X,
    ⟨hL, fun i j h => ?_, fun _ x _ => ?_⟩, fun v e y yt i _ _ => ?_⟩
  · obtain rfl : i = j := Subsingleton.elim (α := PUnit → PUnit) _ _
    have := congrArg (fun u : Γ(Y.X, _)ˣ => fnOf _ h.1 u.val) (hL.g_self i)
    rw [Units.val_one, map_one] at this
    rw [← (this.symm.trans (fnOf_resG _ h.1 _)), _root_.one_mul]
  · rw [smul_zero]
    exact (CartierDiv.isEqn_zero x).iff_unitAt.2 (by simpa using hu x)
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have h := GlobalTheory.TrueGeo.OfLattice.valAt_const y.1 y.2 a
    simp only [PNat.mk_coe, inv_one, one_pow, _root_.one_mul, Units.val_mk0, h]
    field_simp

end GlobalTheory.LineNorm
