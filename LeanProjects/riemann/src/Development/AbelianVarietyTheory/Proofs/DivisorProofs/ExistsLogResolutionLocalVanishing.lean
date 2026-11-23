import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsRoundedDownDivisorStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsLogResolutionBigBundleStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierVanishingNefTwistAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAmpleTensorAmplePowProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.Discrepancy

theorem exists_logRes_subsingleton_cohOn_one : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Z : Closeds X), η ≠ 0 → 0 < m → Z ≠ ⊤ → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (s : Y ⟶ X) (_ : IsDominant s) (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y) (N : CartierDiv X), IsLogRes p n η m G s K B ∧ (∀ y, s y ∈ Z → y ∈ B) ∧ (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) ∧ (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) := by
  intro hPr X _ _ p n hp hn η m G Z hη hm hZ
  letI := algebraΓOfHom p
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have hpS : IsProjOver (strHom ℂ X) := by rwa [strHom_eq (f := p) fun _ => rfl]
  have hbig : IsBig ℂ H := IsAmpleLB.isBig ℂ X hpS H hH
  obtain ⟨Y, _, s, _, K, B, hlog, hZB, a, Fd, A, hA, hFd⟩ :=
    GlobalTheory.T.exists_log_resolution_big_bundle hPr ℂ X p n hp hn η m G hη Z hZ H hH.isLB hbig
  haveI : SmoothOfRelativeDimension n (s ≫ p) := hlog.smooth
  haveI : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_isProjOver hlog.proj
  obtain ⟨F, hF, -⟩ := GlobalTheory.T.exists_rounded_down_divisor ℂ Y (s ≫ p) n hlog.proj (pullCart s G - m • K) m

  obtain ⟨J, hJ⟩ := eventually_atTop.1
    (hH.eventually_isAmpleLB_tens_lbPow_succ (isLB_toLB (-G)))
  have hj : J ≤ m * (J + 1) - 1 := by
    have : J + 1 ≤ m * (J + 1) := Nat.le_mul_of_pos_left _ hm
    omega
  have hTa := hJ _ hj
  have hsucc : m * (J + 1) - 1 + 1 = m * (J + 1) := by
    have : 1 ≤ m * (J + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hm.ne' (Nat.succ_ne_zero J))
    omega
  rw [hsucc] at hTa
  obtain ⟨N, hNc⟩ := toPic_surjective ((J + 2) • cls H hH.isLB)
  have hTn : IsNef ℂ (tens (toLB (-G)) (lbPow H (m * (J + 1)))) := hTa.isNef
  have hcls : cls _ hTn.isLB = (m * 1) • cls (toLB N) (isLB_toLB N) - 1 • toPic G - m • cls H hH.isLB := by
    rw [cls_tens (isLB_toLB (-G)) (isLB_lbPow hH.isLB _), cls_lbPow hH.isLB, ← toPic_apply,
      ← toPic_apply, hNc, map_neg]
    simp only [mul_one, one_smul, smul_smul]
    rw [show m * (J + 2) = m * (J + 1) + m by ring, add_smul]
    abel
  obtain ⟨-, hloc⟩ := GlobalTheory.T.multiplier_vanishing_nef_twist_ample ℂ X p n hp η m G Y s K B F hη hm hlog hF (toLB N) H _
    (isLB_toLB N) hH.isLB 1 hTn one_pos hcls hH.isNef a Fd A hA hFd
  refine ⟨Y, inferInstance, inferInstance, s, inferInstance, K, B, F, N, hlog, hZB, hF,
    fun U hU => ?_⟩
  have hP := pull_isLB (isLB_toLB N) s
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq (GlobalTheory.structureModule Y) (isLB_toLB (-F)) hP
    (isLB_toLB (pullCart s N - F)) (by
      rw [← toPic_apply, ← toPic_apply, cls_pull (isLB_toLB N) s hP, ← toPic_apply,
        ← toPic_pullCart, map_sub, map_neg]
      abel)
  exact (cohOn.mapIso Γ(Y, ⊤) (s ⁻¹ᵁ U) 1 e).toEquiv.subsingleton_congr.1 (hloc U hU 1 one_pos)

end GlobalTheory.Discrepancy
