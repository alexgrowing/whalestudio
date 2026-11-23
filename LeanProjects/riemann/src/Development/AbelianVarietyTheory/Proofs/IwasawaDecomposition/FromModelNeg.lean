import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm

namespace GlobalTheory.LineNorm.Neg

theorem pull_dual_g {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (i j : (L.pull f).ι) :
    ((CechPic.dual L).pull f).g i j = ((L.pull f).g i j)⁻¹ := by
  have key {A B C : Type} [CommGroup A] [CommGroup B] [CommGroup C] (p : B →* C) (q : A →* B) (a : A) :
      ∏ _k : PUnit.{1}, p (q a⁻¹) ^ (1 : ℤ) = (∏ _k : PUnit.{1}, p (q a) ^ (1 : ℤ))⁻¹ := by
    simp
  exact key _ _ (L.g (i PUnit.unit) (j PUnit.unit))

theorem presents_neg {X Y : Scheme.{0}} [IsIntegral Y] {L : LB X} (hL : L.IsLB) (f : Y ⟶ X)
    {D : CartierDiv Y} {r : (L.pull f).ι → Y.functionFieldˣ} (h : Presents D (L.pull f) r) :
    Presents (-D) ((CechPic.dual L).pull f) (fun i => (r i)⁻¹) := by
  refine ⟨LB.isLB_pull (CechPic.isLB_dual hL) f, fun i j hij => ?_, fun i x hx => (h.isEqn i x hx).neg⟩
  have e := h.isRatSec i j hij
  have e' : fnOf _ hij (((CechPic.dual L).pull f).g i j).val = (fnOf _ hij ((L.pull f).g i j).val)⁻¹ :=
    (congrArg (fun u : Γ(Y, (L.pull f).U i ⊓ (L.pull f).U j)ˣ => fnOf _ hij u.val)
      (pull_dual_g L f i j)).trans (map_units_inv _ _)
  refine Eq.trans ?_ (congrArg (· * _) e').symm
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, e, mul_inv]
  rfl

theorem valAt_inv {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] {y : Sp K ⟶ Z}
    {f : Z.functionField} (hf : UnitAt (below y) f) : valAt y f⁻¹ = (valAt y f)⁻¹ := by
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hf
  rw [← map_units_inv, SmallSec.valAt_algebraMap, SmallSec.valAt_algebraMap, map_units_inv]

theorem fromModel_neg (F : Type) [Field F] [NumberField F] (Y : Var F) (Δ : Y.Dv) (t : Y.X → Y.Fnˣ)
    (φ : PtFn Y) (ht : ∀ y, Δ.IsEqn y (t y)) (h : FromModel Y Δ t φ) :
    FromModel Y (-Δ) (fun y => (t y)⁻¹) (fun v e y => -φ v e y) := by
  obtain ⟨M, L, m, r, hL, hP, hφ⟩ := h
  refine ⟨M, CechPic.dual L, m, fun i => (r i)⁻¹, CechPic.isLB_dual hL, ?_, fun v e y yt i hy hi => ?_⟩
  · rw [smul_neg]
    exact presents_neg hL M.j hP
  · have hmem : below y.1 ∈ (L.pull M.j).U i := by
      have h1 : (y.1 ≫ M.j) (IsLocalRing.closedPoint _) ∈ L.U (i PUnit.unit) := by
        rw [← hy]
        exact hi (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hu : UnitAt (below y.1) (((t (below y.1))⁻¹ ^ (m : ℕ) * r i : Y.Fnˣ) : Y.Fn) := by
      have := ((ht (below y.1)).nsmul m).iff_unitAt.1 (hP.isEqn i _ hmem)
      rwa [← Units.val_div_eq_div_val, div_eq_inv_mul, ← inv_pow] at this
    have e1 : (((t (below y.1))⁻¹⁻¹ ^ (m : ℕ) * (r i)⁻¹ : Y.Fnˣ) : Y.Fn) =
        (((t (below y.1))⁻¹ ^ (m : ℕ) * r i : Y.Fnˣ) : Y.Fn)⁻¹ := by
      rw [← Units.val_inv_eq_inv_val, mul_inv, ← inv_pow]
    change ((m : ℕ) : ℝ) * -φ v e y = Real.log (e.w (valAt y.1
      (((t (below y.1))⁻¹⁻¹ ^ (m : ℕ) * (r i)⁻¹ : Y.Fnˣ) : Y.Fn)))
    rw [e1, valAt_inv hu, map_inv₀, Real.log_inv, mul_neg, hφ v e y yt i hy hi]

end GlobalTheory.LineNorm.Neg
