import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open TopologicalSpace

namespace GlobalTheory.Mum

theorem exists_secK_of_iso_pull : ∀ {X X' : Scheme.{0}} (L : LB X) (L' : LB X') (f : X' ⟶ X) (w : LB.Iso L' (L.pull f)), L.IsLB → L'.IsLB → w.IsGen → ∀ (N : ℕ) (t : H0 L' N), ∃ s : SecK L f N, ∀ (Z : Scheme.{0}) (p : Z ⟶ X') (z : Z) J J', Good L z J → Good L' z J' → sval s p z J = (gw w p z (J (p ≫ f)) (J' p) ^ N).val * sval t p z J' := by
  intro X X' L L' f w hL hL' hw N t
  have hp := (isGen_iff w).1 hw
  have mL : ∀ (j : Fin 1 → L.ι) (x : X'), x ∈ LB.wchart L (fun _ : Fin 1 => f) j → f x ∈ L.U (j 0) :=
    fun j x hx => Set.mem_iInter.1 hx 0
  have mL' : ∀ (k : L'.ι) (x : X'), x ∈ L'.U k → x ∈ LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k) :=
    fun k x hx => Set.mem_iInter.2 fun _ => hx
  have indep : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k k' : L'.ι), f (r z) ∈ L.U j → r z ∈ L'.U k →
      r z ∈ L'.U k' →
      (gw w r z j k ^ N).val * gs r z (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)) (t.f (fun _ => k)) =
      (gw w r z j k' ^ N).val * gs r z (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k')) (t.f (fun _ => k')) := by
    intro Z r z j k k' hj hk hk'
    rw [sec_trans t r z (mL' k _ hk) (mL' k' _ hk'), hp Z r z j j k k' hj hj hk hk', gm_self hL (r ≫ f) z hj,
      ← _root_.mul_assoc, ← Units.val_mul, trF, Fin.prod_univ_one, Category.comp_id, zpow_natCast, ← mul_pow, _root_.one_mul,
      mul_right_comm, inv_mul_cancel, _root_.one_mul]
  have glue : ∀ j : Fin 1 → L.ι, ∃ a : Γ(X', LB.wchart L (fun _ : Fin 1 => f) j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (k : L'.ι), r z ∈ LB.wchart L (fun _ : Fin 1 => f) j → r z ∈ L'.U k →
      gs r z _ a = (gw w r z (j 0) k ^ N).val *
        gs r z (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)) (t.f (fun _ => k)) := by
    intro j
    let W : L'.ι → X'.Opens := fun k => LB.wchart L (fun _ : Fin 1 => f) j ⊓ L'.U k
    have l₁ : ∀ k, W k ≤ (L.pull f).U (fun _ => j 0) ⊓ L'.U k := fun k x hx => ⟨mem_pull.2 (mL j x hx.1), hx.2⟩
    have l₂ : ∀ k, W k ≤ LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k) := fun k x hx => mL' k x hx.2
    obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(X', W k), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) k, r z ∈ W k →
        gs r z (W k) (u k) = (gw w r z (j 0) k ^ N).val *
          gs r z (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)) (t.f (fun _ => k)) :=
      ⟨fun k => (res (l₁ k) (w.s (fun _ => j 0, k)) ^ N).val *
          (X'.presheaf.map (homOfLE (l₂ k)).op).hom (t.f (fun _ => k)), fun Z r z k hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans
          (congrArg Units.val ((map_pow _ _ _).trans (congrArg (· ^ N) (gm_res r z (l₁ k) hz _)))))
          (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' W (LB.wchart L (fun _ : Fin 1 => f) j)
      (fun k => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL' y
        exact Opens.mem_iSup.2 ⟨k, hy, hk⟩) u
      (fun k k' => fn_ext (V := W k ⊓ W k') fun y hy => by
        refine (gs_res (𝟙 X') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X') y inf_le_right hy _).symm)
        rw [hu _ _ y k hy.1, hu _ _ y k' hy.2]
        exact indep _ (𝟙 X') y (j 0) k k' (mL j y hy.1.1) hy.1.2 hy.2.2)
    refine ⟨a, fun Z r z k h₁ h₂ => ?_⟩
    have hz : r z ∈ W k := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W k)) (ha k)).trans (hu Z r z k hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J J' hJ hJ' => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL' y
    refine (gs_res (𝟙 X') y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 X') y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 X') y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 X') y j j' hy.1 hy.2)))
      (gs_res (𝟙 X') y _ hy _))).symm)
    refine (ha j _ (𝟙 X') y k hy.1 hk).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 X') y k hy.2 hk)).symm)
    rw [hp _ (𝟙 X') y (j 0) (j' 0) k k (mL j y hy.1) (mL j' y hy.2) hk hk, gm_self hL' (𝟙 X') y hk, inv_one, _root_.mul_one,
      mul_pow, Units.val_mul, _root_.mul_assoc, Fin.prod_univ_one, zpow_natCast]
  · rw [sval_of t r z J' (fun _ => J' r) (fun _ => by rw [Category.comp_id])]
    exact ha _ Z r z (J' r) (hJ.mem (fun _ : Fin 1 => f) r) (hJ' r)

end GlobalTheory.Mum
