import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TriFrame

variable {X : Scheme.{0}} {A : X.Opens} {G : X.Modules} {σ : Fin 1 → Γ(G, A)}

theorem eq_coord_smul_frame (hσ : IsFrame σ) {W : X.Opens} (hW : W ≤ A) (s : Γ(G, W)) :
    s = (hσ.basis hW).repr s 0 • resM G hW (σ 0) := by
  conv_lhs => rw [← (hσ.basis hW).sum_repr s]
  simp [IsFrame.basis_apply]

theorem resM_frame_eq_g_smul (hσ : IsFrame σ) (L : LB X) (ρ : ∀ k, Γ(X, A ⊓ L.U k))
    (hρ : IsGenOn A L ρ) {V V' : X.Opens} {e : Fin 1 → Γ(G, V)} {e' : Fin 1 → Γ(G, V')}
    (k k' : L.ι) (hk : V ≤ L.U k) (hk' : V' ≤ L.U k')
    (hd : coordIn hσ e 0 0 = resG X (le_inf inf_le_right (inf_le_left.trans hk)) (ρ k))
    (hd' : coordIn hσ e' 0 0 = resG X (le_inf inf_le_right (inf_le_left.trans hk')) (ρ k')) :
    resM G (inf_le_left.trans inf_le_right : V ⊓ V' ⊓ A ≤ V') (e' 0) =
      resG X (le_inf (inf_le_left.trans (inf_le_left.trans hk)) (inf_le_left.trans (inf_le_right.trans hk')) :
        V ⊓ V' ⊓ A ≤ L.U k ⊓ L.U k') (L.g k k').val •
        resM G (inf_le_left.trans inf_le_left : V ⊓ V' ⊓ A ≤ V) (e 0) := by
  have hWA : V ⊓ V' ⊓ A ≤ A := inf_le_right
  have c1 : (hσ.basis hWA).repr (resM G (inf_le_left.trans inf_le_left : V ⊓ V' ⊓ A ≤ V) (e 0)) 0 =
      resG X (le_inf hWA (inf_le_left.trans (inf_le_left.trans hk))) (ρ k) := by
    have := hσ.repr_resM (inf_le_right : V ⊓ A ≤ A) (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      V ⊓ V' ⊓ A ≤ V ⊓ A) (resM G inf_le_left (e 0)) 0
    rw [GlobalTheory.Twist.resM_resM] at this
    refine this.trans ?_
    change resG X _ (coordIn hσ e 0 0) = _
    rw [hd, GlobalTheory.LB.resG_resG]
  have c2 : (hσ.basis hWA).repr (resM G (inf_le_left.trans inf_le_right : V ⊓ V' ⊓ A ≤ V') (e' 0)) 0 =
      resG X (le_inf hWA (inf_le_left.trans (inf_le_right.trans hk'))) (ρ k') := by
    have := hσ.repr_resM (inf_le_right : V' ⊓ A ≤ A) (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      V ⊓ V' ⊓ A ≤ V' ⊓ A) (resM G inf_le_left (e' 0)) 0
    rw [GlobalTheory.Twist.resM_resM] at this
    refine this.trans ?_
    change resG X _ (coordIn hσ e' 0 0) = _
    rw [hd', GlobalTheory.LB.resG_resG]
  have hg := hρ k k' (V ⊓ V' ⊓ A) (le_inf hWA (inf_le_left.trans (inf_le_left.trans hk)))
    (le_inf hWA (inf_le_left.trans (inf_le_right.trans hk')))
    (le_inf (inf_le_left.trans (inf_le_left.trans hk)) (inf_le_left.trans (inf_le_right.trans hk')))
  rw [eq_coord_smul_frame hσ hWA (resM G _ (e' 0)), c2, hg, mul_smul, ← c1,
    ← eq_coord_smul_frame hσ hWA]

theorem detUnit_eq_res_g [IsIntegral X] (hσ : IsFrame σ) (L : LB X) (ρ : ∀ k, Γ(X, A ⊓ L.U k))
    (hA : genericPoint X ∈ A) (hρ : IsGenOn A L ρ) {V V' : X.Opens} {e : Fin 1 → Γ(G, V)}
    {e' : Fin 1 → Γ(G, V')} (he : IsFrame e) (he' : IsFrame e')
    (k k' : L.ι) (hk : V ≤ L.U k) (hk' : V' ≤ L.U k')
    (hd : coordIn hσ e 0 0 = resG X (le_inf inf_le_right (inf_le_left.trans hk)) (ρ k))
    (hd' : coordIn hσ e' 0 0 = resG X (le_inf inf_le_right (inf_le_left.trans hk')) (ρ k')) :
    he.detUnit he' (inf_le_left : V ⊓ V' ≤ V) inf_le_right = res (inf_le_inf hk hk') (L.g k k') := by
  refine Units.ext (GlobalTheory.Cartier.ext_germK fun hη => ?_)
  have hηW : genericPoint X ∈ V ⊓ V' ⊓ A := ⟨hη, hA⟩
  rw [← GlobalTheory.Cartier.germ_resG (inf_le_left : V ⊓ V' ⊓ A ≤ V ⊓ V') _ hηW,
    ← GlobalTheory.Cartier.germ_resG (inf_le_left : V ⊓ V' ⊓ A ≤ V ⊓ V') _ hηW]
  congr 1
  rw [← GlobalTheory.LB.val_res, IsFrame.res_detUnit, IsFrame.val_detUnit, GlobalTheory.LB.val_res, GlobalTheory.LB.resG_resG,
    Module.Basis.det_apply, Matrix.det_unique, Module.Basis.toMatrix_apply, Fin.default_eq_zero,
    resM_frame_eq_g_smul hσ L ρ hρ k k' hk hk' hd hd', ← IsFrame.basis_apply he, map_smul,
    Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]

theorem cls_det_eq_of_tri : ∀ (X : Scheme.{0}) [IsIntegral X] (A : X.Opens) (G : X.Modules) (σ : Fin 1 → Γ(G, A)) (hσ : IsFrame σ) (L : LB X) (hL : L.IsLB) (ρ : ∀ k, Γ(X, A ⊓ L.U k)), genericPoint X ∈ A → IsGenOn A L ρ → Tri hσ (fun _ => L) (fun _ => ρ) → ∀ hG : IsVB G 1, CechPic.cls _ hG.isLB_det = CechPic.cls L hL := by
  intro X _ A G σ hσ L hL ρ hA hρ hT hG
  choose V ε k hk hx hε _ hdiag using hT
  let N : LB X := { ι := X, U := V, g := fun x y => (hε x).detUnit (hε y) inf_le_left inf_le_right }
  have hN : N.IsLB := by
    refine ⟨top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩, fun c => ?_, fun c c' c'' => ?_⟩
    · exact (IsFrame.res_detUnit _ _ _ _ _).trans ((hε c).detUnit_self _ _)
    · exact (congrArg₂ (· * ·) (IsFrame.res_detUnit _ _ _ _ _) (IsFrame.res_detUnit _ _ _ _ _)).trans
        ((IsFrame.detUnit_mul _ _ _ _ _ _).trans (IsFrame.res_detUnit _ _ _ _ _).symm)
  have i1 : LBIso N (det G 1) := (lbIso_det_of_frames hN ε hε fun _ _ => rfl).2
  have i2 : LBIso N L := CechPic.iso_of_chart hL ⟨fun x => k x 0, fun x => hk x 0, fun z x y hx' hy' => by
    change gm _ z _ ((hε x).detUnit (hε y) _ _) = _
    rw [detUnit_eq_res_g hσ L ρ hA hρ (hε x) (hε y) (k x 0) (k y 0) (hk x 0) (hk y 0) (hdiag x 0) (hdiag y 0)]
    exact gm_res (𝟙 X) z (inf_le_inf (hk x 0) (hk y 0)) (show z ∈ V x ⊓ V y from ⟨hx', hy'⟩) _⟩
  exact (CechPic.cls_eq_iff _ _).2 (LBIso.trans hG.isLB_det hN hL i1.symm i2)

end GlobalTheory.TriFrame
