import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.ExistsTwistMap
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.IsClosedImmersionLift

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.Amb

theorem isSeparated_pr_zero (k : Type) [CommRing k] (m : ℕ) (n : Fin (m + 1) → ℕ) :
    IsSeparated (pr k m n 0) := by
  have hs : IsSeparated (pr k m n 0 ≫ toSpecBase k (n 0)) := by
    rw [pr_toSpecBase]
    infer_instance
  exact IsSeparated.of_comp _ (toSpecBase k (n 0))

theorem lbIso_pull_tw {k : Type} [CommRing k] {X P : Scheme.{0}} (i : X ⟶ P) {a b : ℕ} (π₁ : P ⟶ PSpace k a)
    (π₀ : P ⟶ PSpace k b) (g : X ⟶ PSpace k a) (e : X ⟶ PSpace k b) (hg : i ≫ π₁ = g) (he : i ≫ π₀ = e) (t : ℕ)
    (M : LB X) (hM : M.IsLB)
    (h : cls ((O1 k a).pull g) (LB.isLB_pull (O1_isLB k a) g) =
      cls M hM + (t : ℤ) • cls ((O1 k b).pull e) (LB.isLB_pull (O1_isLB k b) e)) :
    LBIso ((tw ((O1 k a).pull π₁) ((O1 k b).pull π₀) (-(t : ℤ))).pull i) M := by
  have hA := LB.isLB_pull (O1_isLB k a) π₁
  have hB := LB.isLB_pull (O1_isLB k b) π₀
  have hT := isLB_tw hA hB (-(t : ℤ))
  have hTi := LB.isLB_pull hT i
  rw [← cls_eq_iff hTi hM, cls_pull hT i hTi]
  have hct : cls (tw ((O1 k a).pull π₁) ((O1 k b).pull π₀) (-(t : ℤ))) hT =
      cls ((O1 k a).pull π₁) hA - (-(-(t : ℤ))) • cls ((O1 k b).pull π₀) hB := by
    show cls (((O1 k a).pull π₁).div (AbLaw.pw ((O1 k b).pull π₀) (-(-(t : ℤ))))) hT = _
    rw [cls_div hA (isLB_pw hB _) hT, EffBound.cls_pw hB]
  rw [hct, map_sub, map_zsmul, cls_pull (O1_isLB k a) π₁ hA, cls_pull (O1_isLB k b) π₀ hB,
    ← pull_comp, ← pull_comp, hg, he]
  rw [cls_pull (O1_isLB k a) g, cls_pull (O1_isLB k b) e] at h
  rw [h, neg_neg]
  abel

end GlobalTheory.Amb
