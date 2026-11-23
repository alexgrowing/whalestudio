import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SecTransport

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

section Calc

variable {X X' Y : Scheme.{0}}

theorem chart_le_preimage (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (h : Y ⟶ X') (e : h ≫ F = φ) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => φ) j ≤ h ⁻¹ᵁ (L.pull F).U (fun _ => j 0) := fun y hy =>
  mem_pull.2 ((congrArg (fun q => q y ∈ L.U (j 0)) e).mpr (LB.wchart_le L _ j 0 hy))

def secPullOne (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (h : Y ⟶ X') (e : h ≫ F = φ) (s : LB.Sec (L.pull F)) :
    LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)) where
  f := fun (j : Fin 1 → L.ι) => (h.appLE _ _ (chart_le_preimage L h e j)).hom (s.f (fun _ => j 0))
  compat := fun (j j' : Fin 1 → L.ι) => fn_ext fun y hy => by
    have h₁ : h y ∈ (L.pull F).U (fun _ => j 0) := chart_le_preimage L h e j hy.1
    have h₂ : h y ∈ (L.pull F).U (fun _ => j' 0) := chart_le_preimage L h e j' hy.2
    have g : gm (𝟙 Y) y _ ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)).g j j') =
        gm (𝟙 Y ≫ φ) y (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) :=
      (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2).trans (by rw [Fin.prod_univ_one, zpow_one])
    have eφ : (𝟙 Y ≫ h) ≫ F = 𝟙 Y ≫ φ := by rw [Category.assoc, e]
    exact (gs_res _ y _ hy _).trans ((gs_appLE h _ _ _ (𝟙 _) y hy.1 _).trans ((gs_compat s (𝟙 Y ≫ h) y h₁ h₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
        ((gs_unit _ y _ hy _).trans (congrArg Units.val (g.trans ((congrArg (fun q => gm q y (L.U (j 0) ⊓ L.U (j' 0))
          (L.g (j 0) (j' 0))) eφ).symm.trans (gm_pull_g L F (𝟙 Y ≫ h) y _ _ h₁ h₂).symm))))
        ((gs_res _ y _ hy _).trans (gs_appLE h _ _ _ (𝟙 _) y hy.2 _)))))))

theorem exists_sec_along_iso {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB)
    (hL' : L'.IsLB) (σ : LB.Sec L') : ∃ s : LB.Sec (L.pull F), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z)
      (J : PUnit → L.ι) (k : L'.ι), r z ∈ (L.pull F).U J → r z ∈ L'.U k →
      gs r z _ (s.f J) = (gw w r z (J PUnit.unit) k).val * gs r z _ (σ.f k) := by
  have glue : ∀ J : PUnit → L.ι, ∃ a : Γ(X', (L.pull F).U J), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (k : L'.ι),
      r z ∈ (L.pull F).U J → r z ∈ L'.U k → gs r z _ a = (gw w r z (J PUnit.unit) k).val * gs r z _ (σ.f k) := by
    intro J
    obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(X', (L.pull F).U J ⊓ L'.U k), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) k,
        r z ∈ (L.pull F).U J ⊓ L'.U k → gs r z _ (u k) = (gw w r z (J PUnit.unit) k).val * gs r z _ (σ.f k) :=
      ⟨fun k => (show Γ(X', (L.pull F).U J ⊓ L'.U k) from (w.s (J, k)).val) * resG X' inf_le_right (σ.f k), fun Z r z k hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hz _) (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' (fun k => (L.pull F).U J ⊓ L'.U k) ((L.pull F).U J)
      (fun k => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL' y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩) u
      (fun k k' => fn_ext (V := ((L.pull F).U J ⊓ L'.U k) ⊓ ((L.pull F).U J ⊓ L'.U k')) fun y hy => by
        refine (gs_res (𝟙 X') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X') y inf_le_right hy _).symm)
        have hj : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy.1.1
        rw [hu _ _ y k hy.1, hu _ _ y k' hy.2, gs_compat σ (𝟙 X') y hy.1.2 hy.2.2,
          hw _ (𝟙 X') y (J PUnit.unit) (J PUnit.unit) k k' hj hj hy.1.2 hy.2.2, gm_self hL (𝟙 X' ≫ F) y hj,
          _root_.one_mul, Units.val_mul, _root_.mul_assoc, mul_left_comm (gw w (𝟙 X') y (J PUnit.unit) k').val,
          Units.inv_mul_cancel_left])
    refine ⟨a, fun Z r z k h₁ h₂ => ?_⟩
    have hz : r z ∈ (L.pull F).U J ⊓ L'.U k := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z _) (ha k)).trans (hu Z r z k hz))
  choose a ha using glue
  refine ⟨⟨a, fun (J J' : PUnit → L.ι) => fn_ext fun y hy => ?_⟩, fun Z r z J k => ha J Z r z k⟩
  obtain ⟨k, hk⟩ := exists_chart hL' y
  have hj : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy.1
  have hj' : F y ∈ L.U (J' PUnit.unit) := mem_pull.1 hy.2
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, gm_pull_g L F (𝟙 X') y J J' hy.1 hy.2,
    ha J _ (𝟙 X') y k hy.1 hk, ha J' _ (𝟙 X') y k hy.2 hk,
    hw _ (𝟙 X') y (J PUnit.unit) (J' PUnit.unit) k k hj hj' hk hk, gm_self hL' (𝟙 X') y hk, inv_one, _root_.mul_one,
    Units.val_mul, _root_.mul_assoc]

theorem isUnit_gs_iff (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    IsUnit (gs f y U a) ↔ f y ∈ X.basicOpen a := by
  unfold gs
  rw [dif_pos h]
  have e : y ∈ f ⁻¹ᵁ X.basicOpen a ↔ y ∈ Y.basicOpen (f.app U a) := by
    rw [Scheme.preimage_basicOpen]
  exact (Y.mem_basicOpen (f.app U a) y h).symm.trans e.symm

end Calc

set_option maxHeartbeats 400000 in

theorem exists_sec_nonzero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (t' : SAB H (Sp S)) (m : SABMap t' Xo.univ.t x) (th : t'.PP.L.Sec), (∀ y : Sp S, ∃ q : t'.G.left, t'.G.hom q = y ∧ q ∈ Out.nonzeroLocus th) → ∃ s : LB.Sec (PPx x), SecNZ x s := by
  intro E _ _ _ H Dw l Xo S _ x t' m1 σ' hnz
  obtain ⟨w1, g1, r1, -⟩ := m1.lin
  have hw1 := (isGen_iff w1).1 g1
  have hL := Xo.univ.t.PP.isLB
  have hL' := t'.PP.isLB
  obtain ⟨s1, hs1⟩ := exists_sec_along_iso hw1 hL hL' σ'
  let A := Xo.univ.t.G
  have cond : (snd (Over.mk x) A).left ≫ A.hom = (fst (Over.mk x) A).left ≫ x :=
    (Over.w (snd (Over.mk x) A)).trans (Over.w (fst (Over.mk x) A)).symm
  let h : Gx x ⟶ t'.G.left := m1.cart.1.lift _ _ cond
  have hφ : h ≫ m1.φ = (snd (Over.mk x) A).left := m1.cart.1.lift_fst _ _ cond
  have hh : h ≫ t'.G.hom = (fst (Over.mk x) A).left := m1.cart.1.lift_snd _ _ cond
  let a0 : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk t'.G.hom rfl
  let b0 : Over.mk (t'.G.hom ≫ x) ⟶ A := Over.homMk m1.φ m1.cart.1.w
  let g0 : t'.G.left ⟶ Gx x := (lift a0 b0).left
  have g0f : g0 ≫ (fst (Over.mk x) A).left = t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
  have g0s : g0 ≫ (snd (Over.mk x) A).left = m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
  have hg0 : g0 ≫ h = 𝟙 _ := m1.cart.1.hom_ext (by rw [Category.assoc, hφ, g0s, Category.id_comp])
        (by rw [Category.assoc, hh, g0f, Category.id_comp])
  let s : LB.Sec (PPx x) := secPullOne Xo.univ.t.PP.L h hφ s1
  refine ⟨s, fun p => ?_⟩
  obtain ⟨q, hq, hqn⟩ := hnz p
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hqn
  have hkU : q ∈ t'.PP.L.U k := t'.G.left.basicOpen_le _ hk
  obtain ⟨j, hj⟩ := exists_chart hL (m1.φ q)
  have mg : g0 q ∈ (PPx x).U (fun _ => j) :=
    Set.mem_iInter.2 fun _ => (congrArg (fun r => r q ∈ Xo.univ.t.PP.L.U j) g0s).mpr hj
  refine ⟨g0 q, fun _ => j, (congrArg (fun r => r q) g0f).trans hq, ?_⟩
  refine (isUnit_gs_iff g0 q _ mg _).1 ?_
  have e : gs g0 q _ (s.f (fun _ => j)) = (gw w1 (𝟙 _) q j k).val * gs (𝟙 _) q _ (σ'.f k) := by
    refine (gs_appLE h _ _ (chart_le_preimage _ h hφ _) g0 q mg _).trans ?_
    rw [hg0]
    exact hs1 _ (𝟙 _) q (fun _ => j) k (mem_pull.2 hj) hkU
  rw [e]
  exact (Units.isUnit _).mul ((isUnit_gs_iff (𝟙 _) q _ hkU _).2 hk)

end GlobalTheory.SecTransport
