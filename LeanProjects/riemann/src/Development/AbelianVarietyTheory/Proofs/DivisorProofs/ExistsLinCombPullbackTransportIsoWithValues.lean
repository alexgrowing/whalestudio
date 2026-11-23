import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

section TransportLinComb

variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {K I : Type} [Fintype K] [Fintype I]

theorem transChart_le (ψ : K → (X' ⟶ X)) (σ : I → (Y ⟶ X')) (jN : I × K → L.ι) (jM : I → L'.ι) (i : I) :
    LB.wchart L (fun p : I × K => σ p.1 ≫ ψ p.2) jN ⊓ LB.wchart L' σ jM ≤
      σ i ⁻¹ᵁ (LB.wchart L ψ (fun k => jN (i, k)) ⊓ L'.U (jM i)) :=
  fun _ hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (i, k), Set.mem_iInter.1 hy.2 i⟩

def transIso (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (w : LB.Iso L' (LB.LinComb L ψ δ)) (σ : I → (Y ⟶ X')) (e : I → ℤ) :
    LB.Iso (LB.LinComb L' σ e) (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2)) where
  s P := ∏ i, res (transChart_le ψ σ P.1 P.2 i) (pullU (σ i) _ (w.s (fun k => P.1 (i, k), P.2 i))) ^ e i

theorem gm_transIso (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (w : LB.Iso L' (LB.LinComb L ψ δ)) (σ : I → (Y ⟶ X'))
    (e : I → ℤ) (r : Z ⟶ Y) (z : Z) (P : (I × K → L.ι) × (I → L'.ι))
    (hP : r z ∈ LB.wchart L (fun p : I × K => σ p.1 ≫ ψ p.2) P.1 ⊓ LB.wchart L' σ P.2) :
    gm r z _ ((transIso ψ δ w σ e).s P) = ∏ i, gm (r ≫ σ i) z _ (w.s (fun k => P.1 (i, k), P.2 i)) ^ e i := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans (congrArg (· ^ e i) ?_))
  exact (gm_res r z _ hP _).trans (gm_pull r (σ i) z _ (transChart_le ψ σ P.1 P.2 i hP) _)

theorem isGen_iff_gm' {M : LB Y} (t : LB.Gen M) :
    t.IsGen ↔ ∀ i j y, y ∈ M.U i ⊓ M.U j →
      gm (𝟙 Y) y (M.U i) (t.s i) = gm (𝟙 Y) y (M.U i ⊓ M.U j) (M.g i j) * gm (𝟙 Y) y (M.U j) (t.s j) := by
  constructor
  · intro h i j y hy
    exact (gm_res (𝟙 Y) y _ hy _).symm.trans ((congrArg (gm (𝟙 Y) y _) (h i j)).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))))
  · intro h i j
    exact unit_ext fun y hy => (gm_res (𝟙 Y) y _ hy _).trans ((h i j y hy).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))).symm)

theorem gm_of_isGen (ψ : K → (X' ⟶ X)) (δ : K → ℤ) {w : LB.Iso L' (LB.LinComb L ψ δ)} (hw : w.IsGen)
    (r : Z ⟶ X') (z : Z) (P Q : (K → L.ι) × L'.ι)
    (hm : r z ∈ LB.wchart L ψ P.1 ⊓ L'.U P.2 ⊓ (LB.wchart L ψ Q.1 ⊓ L'.U Q.2)) :
    gm r z _ (w.s P) = ((∏ k, gm (r ≫ ψ k) z (L.U (P.1 k) ⊓ L.U (Q.1 k)) (L.g (P.1 k) (Q.1 k)) ^ δ k) *
      (gm r z _ (L'.g P.2 Q.2))⁻¹) * gm r z _ (w.s Q) := by
  have h := congrArg (gm r z _) (hw P Q)
  exact (gm_res r z _ hm _).symm.trans (h.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_div L' (LB.LinComb L ψ δ) r z P Q hm).trans (congrArg (· * _) (gm_linComb L ψ δ r z _ _ hm.1.1 hm.2.1)))
    (gm_res r z _ hm _))))

theorem isGen_transIso (ψ : K → (X' ⟶ X)) (δ : K → ℤ) {w : LB.Iso L' (LB.LinComb L ψ δ)} (hw : w.IsGen)
    (σ : I → (Y ⟶ X')) (e : I → ℤ) : (transIso ψ δ w σ e).IsGen := by
  refine (isGen_iff_gm' _).2 fun P Q y hy => ?_
  have hd : gm (𝟙 Y) y ((LB.div (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2))
      (LB.LinComb L' σ e)).U P ⊓ (LB.div (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2))
      (LB.LinComb L' σ e)).U Q) ((LB.div (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2))
      (LB.LinComb L' σ e)).g P Q) = _ :=
    gm_div (LB.LinComb L' σ e) (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2)) (𝟙 Y) y P Q hy
  rw [gm_transIso ψ δ w σ e (𝟙 Y) y P hy.1, gm_transIso ψ δ w σ e (𝟙 Y) y Q hy.2,
    hd]
  erw [gm_linComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2) (𝟙 Y) y P.1 Q.1 hy.1.1 hy.2.1,
    gm_linComb L' σ e (𝟙 Y) y P.2 Q.2 hy.1.2 hy.2.2,
    Finset.prod_congr rfl fun i _ => congrArg (· ^ e i) (gm_of_isGen ψ δ hw (𝟙 Y ≫ σ i) y
      (fun k => P.1 (i, k), P.2 i) (fun k => Q.1 (i, k), Q.2 i)
      ⟨transChart_le ψ σ P.1 P.2 i hy.1, transChart_le ψ σ Q.1 Q.2 i hy.2⟩)]
  rw [Fintype.prod_prod_type]
  simp only [Category.assoc, mul_zpow, Finset.prod_mul_distrib, ← Finset.prod_zpow, ← zpow_mul, inv_zpow',
    Finset.prod_inv_distrib]
  simp only [mul_comm (δ _) (e _)]
  simp only [zpow_neg, Finset.prod_inv_distrib]
  rfl

end TransportLinComb

theorem exists_transIso_linComb : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {K I : Type} [Fintype K] [Fintype I]
    (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (w : LB.Iso L' (LB.LinComb L ψ δ)), w.IsGen → L.IsLB → L'.IsLB →
    ∀ (σ : I → (Y ⟶ X')) (e : I → ℤ), ∃ v : LB.Iso (LB.LinComb L' σ e)
      (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2)), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' →
        gm q z _ (v.s (fun p => J (q ≫ σ p.1 ≫ ψ p.2), fun i => J' (q ≫ σ i))) =
          ∏ i, gm (q ≫ σ i) z _ (w.s (fun k => J (q ≫ σ i ≫ ψ k), J' (q ≫ σ i))) ^ e i := by
  intro X X' Y L L' K I _ _ ψ δ w hw _ _ σ e
  refine ⟨transIso ψ δ w σ e, isGen_transIso ψ δ hw σ e, fun Z q z J J' hJ hJ' => ?_⟩
  exact gm_transIso ψ δ w σ e q z _ ⟨hJ.mem (fun p : I × K => σ p.1 ≫ ψ p.2) q, hJ'.mem σ q⟩

end GlobalTheory.Mum
