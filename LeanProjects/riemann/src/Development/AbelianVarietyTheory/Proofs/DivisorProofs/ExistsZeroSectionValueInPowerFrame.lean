import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUnivVals

open TopologicalSpace Opposite

theorem comp_base_pt {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g).base x = g.base (f.base x) := rfl

theorem glue_fn {X : Scheme.{0}} {J : Type} (W : J → X.Opens) (hc : (⊤ : X.Opens) ≤ iSup W) (a : ∀ i, Γ(X, W i))
    (h : ∀ i j x, x ∈ W i → x ∈ W j → gs (𝟙 X) x (W i) (a i) = gs (𝟙 X) x (W j) (a j)) :
    ∃ α : Γ(X, ⊤), ∀ i x, x ∈ W i → gs (𝟙 X) x ⊤ α = gs (𝟙 X) x (W i) (a i) := by
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W ⊤ (fun i => homOfLE le_top) hc a
    (fun i j => fn_ext (V := W i ⊓ W j) fun y hy =>
      (gs_res (𝟙 X) y inf_le_left hy _).trans ((h i j y hy.1 hy.2).trans (gs_res (𝟙 X) y inf_le_right hy _).symm))
  refine ⟨s, fun i x hx => ?_⟩
  exact (gs_res (𝟙 X) x (le_top : W i ≤ ⊤) hx s).symm.trans (congrArg (gs (𝟙 X) x (W i)) (hs i))

theorem vals (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ)
    (eA : LB.Gen (L.pull (eSec A))) (s : LB.Sec (LPow A L (k : ℤ) (topS Rg))) (hL : L.IsLB) (hA : eA.IsGen) :
    ∃ α : Γ(Sp Rg, ⊤), GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) s α := by
  set S : Scheme.{0} := (𝟙_ (Over (Sp Rg))).left with hS
  set e : S ⟶ (topS Rg ⊗ A).left := eSec A ≫ θ A with he_def
  have he : e ≫ (snd (topS Rg) A).left = eSec A := by
    rw [he_def, Category.assoc, θ_snd, Category.comp_id]
  have memN : ∀ (z : S) (q : Fin 1 → L.ι), e z ∈ (LPow A L (k : ℤ) (topS Rg)).U q ↔ eSec A z ∈ L.U (q 0) := by
    intro z q
    constructor
    · intro h
      have h0 := Set.mem_iInter.1 h 0
      rw [Set.mem_preimage, ← comp_base_pt, he] at h0
      exact h0
    · intro h
      refine Set.mem_iInter.2 fun t => ?_
      rw [Subsingleton.elim t 0, Set.mem_preimage, ← comp_base_pt, he]
      exact h
  let W : L.ι → S.Opens := fun i => e ⁻¹ᵁ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (L.pull (eSec A)).U (fun _ => i)
  have memW : ∀ (z : S) (i : L.ι), z ∈ W i ↔ eSec A z ∈ L.U i := by
    intro z i
    constructor
    · intro h; exact mem_pull.1 h.2
    · intro h; exact ⟨(memN z _).2 h, mem_pull.2 h⟩
  let a : ∀ i, Γ(S, W i) := fun i =>
    (S.presheaf.map (homOfLE (inf_le_left : W i ≤ e ⁻¹ᵁ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => i))).op).hom ((e.app _).hom (s.f (fun _ => i))) *
      ((res (inf_le_right : W i ≤ (L.pull (eSec A)).U (fun _ => i)) (eA.s (fun _ => i)))⁻¹ ^ k).val
  have ga : ∀ i x, x ∈ W i → gs (𝟙 S) x (W i) (a i) =
      gs e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => i)) (s.f (fun _ => i)) * ((gm (𝟙 S) x _ (eA.s (fun _ => i)))⁻¹ ^ k).val := by
    intro i x hx
    rw [gs_mul (𝟙 S) x _ hx, gs_res (𝟙 S) x _ hx, gs_pull (𝟙 S) e x _ hx.1, Category.id_comp, gs_unit (𝟙 S) x _ hx,
      map_pow, map_inv, gm_res (𝟙 S) x _ hx]

  have compat : ∀ i j x, x ∈ W i → x ∈ W j → gs (𝟙 S) x (W i) (a i) = gs (𝟙 S) x (W j) (a j) := by
    intro i j x hx hy
    have hxi := (memW x i).1 hx
    have hxj := (memW x j).1 hy
    have hx' : e x ∈ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => j) := ⟨hx.1, hy.1⟩
    have mem : (snd (topS Rg) A).left (e x) ∈ L.U i ⊓ L.U j := by
      rw [← comp_base_pt, he]; exact ⟨hxi, hxj⟩
    have hg : gm e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => j)) ((LPow A L (k : ℤ) (topS Rg)).g (fun _ => i) (fun _ => j)) =
        (gm (eSec A) x _ (L.g i j)) ^ k := by
      show gm e x _ (∏ _t : Fin 1, (res _ (pullU (snd (topS Rg) A).left _ (L.g i j))) ^ (k : ℤ)) = _
      rw [Fintype.prod_unique, map_zpow]
      erw [gm_res e x _ hx']
      rw [gm_pull e _ x _ mem, he, zpow_natCast]
    have hs := congrArg (gs e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => j))) (s.compat (fun _ => i) (fun _ => j))
    rw [gs_res e x _ hx', gs_mul e x _ hx', gs_res e x _ hx', gs_unit e x _ hx', hg] at hs
    have hp : x ∈ (L.pull (eSec A)).U (fun _ => i) ⊓ (L.pull (eSec A)).U (fun _ => j) := ⟨hx.2, hy.2⟩
    have mem' : (eSec A) ((𝟙 S : S ⟶ S) x) ∈ L.U i ⊓ L.U j := ⟨hxi, hxj⟩
    have hg' : gm (𝟙 S) x _ ((L.pull (eSec A)).g (fun _ => i) (fun _ => j)) = gm (eSec A) x _ (L.g i j) := by
      show gm (𝟙 S) x _ (∏ _t : PUnit, (res _ (pullU (eSec A) _ (L.g i j))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      erw [gm_res (𝟙 S) x _ hp]
      rw [gm_pull (𝟙 S) (eSec A) x _ mem', Category.id_comp]
    have hA' := congrArg (gm (𝟙 S) x ((L.pull (eSec A)).U (fun _ => i) ⊓ (L.pull (eSec A)).U (fun _ => j)))
      (hA (fun _ => i) (fun _ => j))
    rw [map_mul, gm_res _ x _ hp, gm_res _ x _ hp, hg'] at hA'
    rw [ga i x hx, ga j x hy, hs, hA']
    set u := gm (eSec A) x _ (L.g i j)
    set B := gm (𝟙 S) x _ (eA.s (fun _ => j))
    have hinv : (u * B)⁻¹ ^ k = (u ^ k)⁻¹ * B⁻¹ ^ k := by rw [mul_inv, mul_pow, inv_pow]
    have hU : (u ^ k).val * ((u ^ k)⁻¹).val = 1 := Units.mul_inv _
    rw [hinv, Units.val_mul]
    linear_combination (gs e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => j)) (s.f (fun _ => j)) * (B⁻¹ ^ k).val) * hU
  obtain ⟨α, hα⟩ := glue_fn W (fun x _ => by
      obtain ⟨i, hi⟩ := exists_chart hL (eSec A x)
      exact Opens.mem_iSup.2 ⟨i, (memW x i).2 hi⟩) a compat
  refine ⟨α, fun z q hz => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, q = fun _ => i := ⟨q 0, funext fun t => by rw [Subsingleton.elim t 0]⟩
  have hzW : z ∈ W i := (memW z i).2 ((memN z _).1 hz)
  rw [hα i z hzW, ga i z hzW]
  show _ = _ * ((gm (𝟙 S) z _ (eA.s fun _ => i)) ^ k).val
  rw [_root_.mul_assoc, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, _root_.mul_one]

end GlobalTheory.HomFixUnivVals
