import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLineBundleOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsVeryAmpleH1Zero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.CancelPow

variable {X Y : Scheme.{0}}

theorem pw_tw (M H : LB X) (t a : ℤ) : AbLaw.pw (tw M H t) a = tw (AbLaw.pw M a) H (t * a) := by
  have : (AbLaw.pw (tw M H t) a).g = (tw (AbLaw.pw M a) H (t * a)).g := by
    funext p q
    change (res _ (M.g p.1 q.1) * (res _ (H.g p.2 q.2 ^ (-t)))⁻¹) ^ a =
      res _ (M.g p.1 q.1 ^ a) * (res _ (H.g p.2 q.2 ^ (-(t * a))))⁻¹
    simp only [map_zpow, map_inv, zpow_neg, inv_inv, zpow_mul]
    exact mul_zpow _ _ _
  exact congrArg (fun g => (⟨(tw M H t).ι, (tw M H t).U, g⟩ : LB X)) this

theorem lbIso_tw_congr_right {A H H' : LB X} (hA : A.IsLB) (t : ℤ) (h : LBIso H H') :
    LBIso (tw A H t) (tw A H' t) := by
  obtain ⟨w, hw⟩ := h
  have l₁ : ∀ p : (A.ι × H'.ι) × (A.ι × H.ι), (tw A H' t).U p.1 ⊓ (tw A H t).U p.2 ≤ A.U p.1.1 ⊓ A.U p.2.1 :=
    fun p x hx => ⟨hx.1.1, hx.2.1⟩
  have l₂ : ∀ p : (A.ι × H'.ι) × (A.ι × H.ι), (tw A H' t).U p.1 ⊓ (tw A H t).U p.2 ≤ H'.U p.1.2 ⊓ H.U p.2.2 :=
    fun p x hx => ⟨hx.1.2, hx.2.2⟩
  have v : ∀ (x : X) (p : (A.ι × H'.ι) × (A.ι × H.ι)), x ∈ (tw A H' t).U p.1 ⊓ (tw A H t).U p.2 →
      gm (𝟙 X) x _ (res (l₁ p) (A.g p.1.1 p.2.1) * res (l₂ p) (w.s (p.1.2, p.2.2)) ^ t) =
        gm (𝟙 X) x _ (A.g p.1.1 p.2.1) * gm (𝟙 X) x (H'.U p.1.2 ⊓ H.U p.2.2) (w.s (p.1.2, p.2.2)) ^ t :=
    fun x p hx => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x _ hx _)
      ((map_zpow _ _ _).trans (congrArg (· ^ t) (gm_res _ x _ hx _))))
  refine GlobalTheory.LBAlg.lbIso_of_germs (fun p => res (l₁ p) (A.g p.1.1 p.2.1) * res (l₂ p) (w.s (p.1.2, p.2.2)) ^ t)
    fun x p q h₁ h₂ h₃ h₄ => ?_
  refine (v x p ⟨h₁, h₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (GlobalTheory.LBAlg.gm_tw A H' t (𝟙 X) x p.1 q.1 ⟨h₁, h₃⟩) (congrArg (·⁻¹) (GlobalTheory.LBAlg.gm_tw A H t (𝟙 X) x p.2 q.2 ⟨h₂, h₄⟩)))
    (v x q ⟨h₃, h₄⟩)).symm)
  rw [GlobalTheory.LBAlg.germs_of_isGen hw x (p.1.2, p.2.2) (q.1.2, q.2.2) h₁.2 h₂.2 h₃.2 h₄.2,
    ← gm_cocycle hA (𝟙 X) x h₁.1 h₂.1 h₃.1, ← gm_cocycle hA (𝟙 X) x h₂.1 h₃.1 h₄.1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem cancel_pw : (∀ (X Y : Scheme.{0}) (b : Y ⟶ X) (H M : LB X) (N : LB Y) (a : ℤ), H.IsLB → M.IsLB → N.IsLB → LBIso (GlobalTheory.AbLaw.pw N a) (H.pull b) → LBIso (GlobalTheory.AbLaw.pw N (a + 1)) (M.pull b) → LBIso N ((GlobalTheory.AbLaw.tw M H (-1)).pull b)) ∧ ∀ (X : Scheme.{0}) (H M : LB X) (a : ℤ), H.IsLB → M.IsLB → LBIso (GlobalTheory.AbLaw.pw H (a + 1)) (GlobalTheory.AbLaw.pw M a) → LBIso H (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.tw M H (-1)) a) := by
  refine ⟨fun X Y b H M N a hH hM hN e₁ e₂ => ?_, fun X H M a hH hM e => ?_⟩
  · have hP : (M.pull b).IsLB := pull_isLB hM b
    have hQ : (H.pull b).IsLB := pull_isLB hH b
    have k₁ : LBIso N (tw (tw N (H.pull b) 1) (H.pull b) (-1)) := GlobalTheory.LBAlg.lbIso_tw_tw hN hQ 1
    have k₂ : LBIso (tw N (H.pull b) 1) (tw N (AbLaw.pw N a) 1) := lbIso_tw_congr_right hN 1 e₁.symm
    have k₃ : tw N (AbLaw.pw N a) 1 = tw N N a := by
      simp only [tw, GlobalTheory.Algebraise.pw_pw]
      congr 2
      ring
    have k₄ : LBIso (tw N N a) (M.pull b) :=
      LBIso.trans (isLB_tw hN hN a) (isLB_pw hN (a + 1)) hP (GlobalTheory.Algebraise.lbIso_tw hN a).symm e₂
    have k₅ : LBIso (tw N (H.pull b) 1) (M.pull b) :=
      LBIso.trans (isLB_tw hN hQ 1) (isLB_tw hN (isLB_pw hN a) 1) hP k₂ (k₃ ▸ k₄)
    have k₆ : LBIso (tw (tw N (H.pull b) 1) (H.pull b) (-1)) (tw (M.pull b) (H.pull b) (-1)) :=
      GlobalTheory.LBAlg.lbIso_tw_congr hQ (-1) k₅
    have k₇ : LBIso (tw (M.pull b) (H.pull b) (-1)) ((tw M H (-1)).pull b) :=
      LBIso.chartPull (GlobalTheory.LBAlg.chartPullTw (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M b b rfl)
          (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull H b b rfl) (-1))
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (tw M H (-1)) b b rfl) (GlobalTheory.LBAlg.lbIso_self (isLB_tw hM hH (-1)))
    exact LBIso.trans hN (isLB_tw (isLB_tw hN hQ 1) hQ (-1)) (pull_isLB (isLB_tw hM hH (-1)) b) k₁
      (LBIso.trans (isLB_tw (isLB_tw hN hQ 1) hQ (-1)) (isLB_tw hP hQ (-1)) (pull_isLB (isLB_tw hM hH (-1)) b) k₆ k₇)
  · have h₁ : LBIso (tw H H a) (AbLaw.pw M a) :=
      LBIso.trans (isLB_tw hH hH a) (isLB_pw hH (a + 1)) (isLB_pw hM a) (GlobalTheory.Algebraise.lbIso_tw hH a).symm e
    have h₂ : LBIso (tw (tw H H a) H (-a)) (tw (AbLaw.pw M a) H (-a)) := GlobalTheory.LBAlg.lbIso_tw_congr hH (-a) h₁
    have h₃ : AbLaw.pw (tw M H (-1)) a = tw (AbLaw.pw M a) H (-a) := by
      rw [pw_tw]
      congr 1
      ring
    rw [h₃]
    exact LBIso.trans hH (isLB_tw (isLB_tw hH hH a) hH (-a)) (isLB_tw (isLB_pw hM a) hH (-a))
      (GlobalTheory.LBAlg.lbIso_tw_tw hH hH a) h₂

end GlobalTheory.CancelPow
