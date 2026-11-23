import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasWtZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gm_chartPull_g {Y Y' Z : Scheme.{0}} {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (r : Z ⟶ Y') (z : Z) (i j : A'.ι) (hi : r z ∈ A'.U i) (hj : r z ∈ A'.U j) :
    gm r z (A'.U i ⊓ A'.U j) (A'.g i j) =
      gm (r ≫ h) z (A.U (a.idx i) ⊓ A.U (a.idx j)) (A.g (a.idx i) (a.idx j)) := by
  have le : A'.U i ⊓ A'.U j ≤ h ⁻¹ᵁ (A.U (a.idx i) ⊓ A.U (a.idx j)) := fun y hy => ⟨a.le i hy.1, a.le j hy.2⟩
  have e : A'.g i j = res le (pullU h _ (A.g (a.idx i) (a.idx j))) := unit_ext fun y hy =>
    (a.g y i j hy.1 hy.2).trans ((gm_res (𝟙 Y') y le hy _).trans
      ((gm_pull (𝟙 Y') h y _ (le hy) _).trans (by rw [Category.id_comp]))).symm
  have hm : r z ∈ A'.U i ⊓ A'.U j := ⟨hi, hj⟩
  rw [e]
  exact (gm_res r z le hm _).trans (gm_pull r h z _ (le hm) _)

theorem exists_red : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → FormEq (Sum.elim (fun a => Φ.D.q.left ≫ ψ a) φt) (Sum.elim ε εt) (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) → ∀ b : LB.Sec (LB.LinComb L ψ ε), ∃ φ : (Φ.H 1).Sec, UFib.Red Φ c t b φ := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t ht hF b
  obtain ⟨s, hs⟩ := exists_sec hL hF (pullMulSec b Φ.D.q.left t ht)
  have le : ∀ l : Φ.N₀.ι, Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l ≤
      LB.wchart L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => c.idx l) :=
    fun l y hy => Set.mem_iInter.2 fun _ => c.le l hy
  refine ⟨⟨fun l => (Φ.G.left.presheaf.map (homOfLE (le l)).op).hom (s.f (fun _ => c.idx l)),
    fun l l' => fn_ext fun y hy => ?_⟩, fun Z r z J hJ l hl e => ?_⟩
  · refine ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le l) hy.1 _)).trans
      ((sec_trans s (𝟙 _) y (le l hy.1) (le l' hy.2)).trans (Eq.trans ?_ ((gs_mul (𝟙 _) y _ hy _ _).trans
        (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _)
          ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le l') hy.2 _)))).symm))
    refine congrArg₂ (· * ·) (congrArg Units.val ?_) rfl
    have e₁ := gm_chartPull_g c (𝟙 _ ≫ Φ.D.q.left) y l l' hy.1 hy.2
    have e₂ := gm_pull (𝟙 _) Φ.D.q.left y (Φ.N₀.U l ⊓ Φ.N₀.U l') ⟨hy.1, hy.2⟩ (Φ.N₀.g l l')
    refine Eq.trans ?_ (((congrArg (gm (𝟙 _) y _) (pow_one _)).trans e₂).trans e₁).symm
    refine Eq.trans ?_ (map_pow _ _ _).symm
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rw [Category.assoc]
    rfl
  · refine (gs_res r z (le l) hl _).trans ?_
    rw [← sval_pullMulSec b Φ.D.q.left t ht r z hJ, ← hs Z r z J hJ]
    exact (sval_of s r z J (fun _ => c.idx l) (fun _ => e)).symm

end GlobalTheory.ZH.UFib
end
