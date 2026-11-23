import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogKSCoc

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by
  ext
  change (X.presheaf.map _).hom ((X.presheaf.map _).hom _) = (X.presheaf.map _).hom _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_intertwines {Y : Scheme.{0}} {P Q A B V : Y.Opens} (a : Γ(Y, P)ˣ) (a' : Γ(Y, Q)ˣ) (m : Γ(Y, A)ˣ)
    (l : Γ(Y, B)ˣ) (hA : P ⊓ Q ≤ A) (hB : P ⊓ Q ≤ B)
    (e : res (inf_le_left : P ⊓ Q ≤ P) a = res hA m * (res hB l)⁻¹ * res (inf_le_right : P ⊓ Q ≤ Q) a')
    (h : V ≤ P) (h' : V ≤ Q) (hM : V ≤ A) (hL : V ≤ B) :
    res hM m * res h' a' = res h a * res hL l := by
  have e' := congrArg (res (le_inf h h')) e
  simp only [map_mul, map_inv, res_res] at e'
  rw [e', _root_.mul_right_comm, inv_mul_cancel_right]

theorem gen_intertwines {Y : Scheme.{0}} (M L : LB Y) (w : LB.Iso L M) (hw : w.IsGen) (i i' : M.ι) (k k' : L.ι)
    {V : Y.Opens} (h : V ≤ M.U i ⊓ L.U k) (h' : V ≤ M.U i' ⊓ L.U k') (hM : V ≤ M.U i ⊓ M.U i')
    (hL : V ≤ L.U k ⊓ L.U k') :
    res hM (M.g i i') * res h' (w.s (i', k')) = res h (w.s (i, k)) * res hL (L.g k k') := by
  exact res_intertwines (w.s (i, k)) (w.s (i', k')) (M.g i i') (L.g k k') _ _ (hw (i, k) (i', k')) h h' hM hL

theorem iso_pull_intertwines : ∀ (Y Z : Scheme.{0}) (φ : Y ⟶ Z) (L : LB Z) (L' : LB Y) (w : LB.Iso L' (L.pull φ)), w.IsGen → ∀ (i i' : L.ι) (k k' : L'.ι) (O O' : Y.Opens) (hO : O ≤ (L.pull φ).U (fun _ => i) ⊓ L'.U k) (hO' : O' ≤ (L.pull φ).U (fun _ => i') ⊓ L'.U k') (hk : O ≤ L'.U k) (hk' : O' ≤ L'.U k') (hu : O ⊓ O' ≤ φ ⁻¹ᵁ (L.U i ⊓ L.U i')), resG Y hu (pullU φ _ (L.g i i')).val * resG Y (inf_le_right : O ⊓ O' ≤ O') (resG Y hO' (w.s (fun _ => i', k')).val) = resG Y (inf_le_left : O ⊓ O' ≤ O) (resG Y hO (w.s (fun _ => i, k)).val) * resG Y (inf_le_inf hk hk') (L'.g k k').val := by
  intro Y Z φ L L' w hw i i' k k' O O' hO hO' hk hk' hu
  have e := gen_intertwines (L.pull φ) L' w hw (fun _ => i) (fun _ => i') k k' (V := O ⊓ O')
    (inf_le_left.trans hO) (inf_le_right.trans hO')
    (inf_le_inf (hO.trans inf_le_left) (hO'.trans inf_le_left)) (inf_le_inf hk hk')
  have g : res (inf_le_inf (hO.trans inf_le_left) (hO'.trans inf_le_left))
      ((L.pull φ).g (fun _ => i) (fun _ => i')) = res hu (pullU φ _ (L.g i i')) := by
    unfold LB.pull LB.LinComb
    dsimp only
    rw [Fintype.prod_unique, zpow_one]
    exact res_res _ _ _
  rw [g] at e
  have e₁ := congrArg Units.val (res_res hO (inf_le_left : O ⊓ O' ≤ O) (w.s (fun _ => i, k)))
  have e₂ := congrArg Units.val (res_res hO' (inf_le_right : O ⊓ O' ≤ O') (w.s (fun _ => i', k')))
  exact (congrArg (_ * ·) e₂).trans ((congrArg Units.val e).trans (congrArg (· * _) e₁.symm))

end GlobalTheory.LogKSCoc
