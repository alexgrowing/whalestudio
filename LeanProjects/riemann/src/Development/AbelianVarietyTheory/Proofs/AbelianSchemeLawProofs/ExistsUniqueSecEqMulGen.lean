import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EvVal

theorem existsUnique_sec_eq_mul_gen {Y : Scheme.{0}} (M : LB Y) (hc : ⨆ j, M.U j = ⊤)
    (s : LB.Sec M) (t : LB.Gen M) (ht : t.IsGen) :
    ∃! v : Γ(Y, ⊤), ∀ j, s.f j =
      (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom v * (t.s j).val := by
  obtain ⟨v, hv⟩ := TLinPf.glue M.U hc (fun j => s.f j * ((t.s j)⁻¹).val) (fun i j => by
    have e := congrArg (fun x : Γ(Y, M.U i ⊓ M.U j)ˣ => (x⁻¹).val) (ht i j)
    simp only [mul_inv, ← map_inv, Units.val_mul] at e
    rw [map_mul, map_mul, s.compat i j]
    refine (congrArg (_ * ·) e).trans ?_
    rw [_root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul]
    rfl)
  refine ⟨v, fun j => ?_, fun w hw => TLinPf.eq_local M.U hc _ _ fun j => ?_⟩
  · rw [hv j, Units.inv_mul_cancel_right]
  · rw [hv j, hw j, Units.mul_inv_cancel_right]

def pullSec {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Y' ⟶ Y) (ψ : K → (Y' ⟶ X)) (e : ∀ k, h ≫ φ k = ψ k)
    (le : ∀ j, LB.wchart L ψ j ≤ h ⁻¹ᵁ LB.wchart L φ j) (s : LB.Sec (LB.LinComb L φ ε)) :
    LB.Sec (LB.LinComb L ψ ε) where
  f := fun j => (Y'.presheaf.map (homOfLE (le j)).op).hom ((h.app _).hom (s.f j))
  compat := fun (j j' : K → L.ι) => Geo.Tor.fn_ext fun y hy => by
    have v : ∀ j : K → L.ι, y ∈ LB.wchart L ψ j →
        Geo.Tor.gs (𝟙 Y') y _ ((Y'.presheaf.map (homOfLE (le j)).op).hom ((h.app _).hom (s.f j))) =
        Geo.Tor.gs (𝟙 Y' ≫ h) y (LB.wchart L φ j) (s.f j) := fun j hj =>
      (Geo.Tor.gs_res _ y _ hj _).trans (Geo.Tor.gs_pull _ h y _ (le j hj) _)
    refine ((Geo.Tor.gs_res (𝟙 Y') y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_
      ((Geo.Tor.gs_mul (𝟙 Y') y _ hy _ _).trans
      (congrArg₂ (· * ·) ((Geo.Tor.gs_unit (𝟙 Y') y _ hy _).trans
        (congrArg Units.val (Geo.Tor.gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2)))
        ((Geo.Tor.gs_res (𝟙 Y') y _ hy _).trans (v j' hy.2)))).symm)
    rw [Geo.Tor.sec_trans s (𝟙 Y' ≫ h) y (le j hy.1) (le j' hy.2)]
    simp only [Geo.Tor.trF, Category.assoc, e]

theorem powFrame_isGen {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {T : Over S}
    (z : T ⟶ A)
    (e : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => 1)))
    (he : e.IsGen) (k : ℤ) : (powFrame A L z e k).IsGen := by
  intro i j
  have h := congrArg (· ^ k) (he i j)
  simp only [mul_zpow, ← map_zpow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl

theorem evValSt : ∀ S : Scheme.{0}, EvValSt (S := S) := by
  intro S P N T z e he s
  exact existsUnique_sec_eq_mul_gen _ (TLinPf.linComb_cover P.L P.isLB _ _)
    (pullSec P.L (fun _ : Fin 1 => (snd T P.A).left) (fun _ => (N : ℤ)) (ptSecT P.A z).left
      (fun _ => z.left) (fun _ => by rw [← Over.comp_left, ptSecT, lift_snd])
      (val_le P.A P.L z) s)
    (powFrame P.A P.L z e N) (powFrame_isGen P.A P.L z e he N)

end GlobalTheory.EvVal
