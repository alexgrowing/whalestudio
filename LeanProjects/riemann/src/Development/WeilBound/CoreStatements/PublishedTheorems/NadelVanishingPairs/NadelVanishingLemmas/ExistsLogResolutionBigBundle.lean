import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.BigLineBundleKodairaOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorPullbackSupportAndEffectiveStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsSmoothProjectiveModel
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsEmbeddedResolutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullTopInjective
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
namespace GlobalTheory.LogResBig

theorem supp_nsmul_le {Y : Scheme.{0}} [IsIntegral Y] (D : CartierDiv Y) : ∀ c : ℕ, (c • D).supp ≤ D.supp
  | 0 => by
    rw [zero_smul, CartierDiv.supp_eq_bot_iff.2 rfl]
    exact bot_le
  | c + 1 => by
    rw [succ_nsmul]
    exact (CartierDiv.supp_add_le _ _).trans (sup_le (supp_nsmul_le D c) le_rfl)

theorem eff_nsmul {Y : Scheme.{0}} [IsIntegral Y] {D : CartierDiv Y} (hD : D.Eff) : ∀ c : ℕ, (c • D).Eff
  | 0 => by
    rw [zero_smul]
    exact CartierDiv.eff_zero
  | c + 1 => by
    rw [succ_nsmul]
    exact (eff_nsmul hD c).add hD

theorem exists_logRes_smul_eq_ample_add_eff :
    GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X), η ≠ 0 → ∀ Z : Closeds X, Z ≠ ⊤ → ∀ (M : LB X) (hM : M.IsLB), (letI := algebraΓOfHom p; IsBig k M) → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (s : Y ⟶ X) (_ : IsDominant s) (K : CartierDiv Y) (B : Closeds Y), IsLogRes p n η m G s K B ∧ (∀ y, s y ∈ Z → y ∈ B) ∧ ∃ (a : ℕ) (Fd : CartierDiv Y) (A : LB Y) (hA : IsAmpleLB A), 0 < a ∧ Fd.Eff ∧ Fd.supp ≤ B ∧ a • CechPic.pull s (cls M hM) = cls A hA.isLB + toPic Fd := by
  intro hP k _ _ X _ p n hp hdim η m G hη Z hZ M hM hbig
  obtain ⟨Y₀, _, s₀, _, hsm, hpr, hbir⟩ := GlobalTheory.T.exists_smooth_projective_birational_model hP k X p n hp hdim
  have hdim₀ : topologicalKrullDim Y₀ = topologicalKrullDim X := by
    rw [hdim]
    exact GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (s₀ ≫ p) n hsm
  have hbig₀ := GlobalTheory.PullBig.isBig_pull k Y₀ X p s₀ hp hpr hdim₀ s₀.denseRange M hbig
  obtain ⟨A, hA⟩ := GlobalTheory.exists_isAmpleLB_of_isProjOver hpr
  obtain ⟨a₀, D₀, ha₀, hD₀, e₀⟩ := GlobalTheory.T.big_line_bundle_kodaira_of_isProjOver k Y₀ (s₀ ≫ p) hpr (M.pull s₀) A hbig₀ hA
  let Zp : Closeds Y₀ := ⟨s₀ ⁻¹' (Z : Set X), Z.isClosed.preimage s₀.continuous⟩
  have hZ' : Zp ⊔ D₀.supp ≠ ⊤ := by
    intro htop
    have hg : genericPoint Y₀ ∈ ((Zp ⊔ D₀.supp : Closeds Y₀) : Set Y₀) := by
      rw [htop]; trivial
    rw [Closeds.coe_sup] at hg
    rcases hg with hg | hg
    · apply hZ
      have hall : Set.univ ⊆ (Zp : Set Y₀) :=
        ((genericPoint_spec Y₀).mem_closed_set_iff Zp.isClosed).1 hg
      have hrange : Set.range s₀ ⊆ (Z : Set X) := by
        rintro _ ⟨y, rfl⟩
        exact hall (Set.mem_univ y)
      have hcl : closure (Set.range s₀) ⊆ (Z : Set X) := closure_minimal hrange Z.isClosed
      rw [s₀.denseRange.closure_range] at hcl
      exact Closeds.ext (Set.eq_univ_of_univ_subset hcl)
    · exact CartierDiv.genericPoint_notMem_supp D₀ hg
  obtain ⟨Y, _, t, _, K, B, hres, hB, c, E, A₁, hA₁, hc, hE, hEB, e₁⟩ :=
    GlobalTheory.T.exists_embedded_resolution hP k X p n η m G hη Y₀ s₀ hsm hpr hbir (Zp ⊔ D₀.supp) hZ' A hA
  have hmem : ∀ y : Y, t y ∈ Zp ∨ t y ∈ D₀.supp → y ∈ B := fun y h => by
    apply hB y
    show t y ∈ ((Zp ⊔ D₀.supp : Closeds Y₀) : Set Y₀)
    rw [Closeds.coe_sup]
    exact h
  refine ⟨Y, inferInstance, t ≫ s₀, inferInstance, K, B, hres, ?_, c * a₀, E + c • pullCart t D₀, A₁, hA₁,
    Nat.mul_pos hc ha₀, hE.add (eff_nsmul ((GlobalTheory.T.cartierDivisorPullback_support_and_effective Y₀ Y t D₀).2 hD₀) c), ?_, ?_⟩
  · intro y hy
    refine hmem y (Or.inl ?_)
    show s₀ (t y) ∈ (Z : Set X)
    simpa using hy
  · refine (CartierDiv.supp_add_le _ _).trans (sup_le hEB ((supp_nsmul_le _ c).trans ?_))
    intro y hy
    exact hmem y (Or.inr ((GlobalTheory.T.cartierDivisorPullback_support_and_effective Y₀ Y t D₀).1 y hy))
  · have e₀' : a₀ • CechPic.pull s₀ (cls M hM) = cls A hA.isLB + toPic D₀ := e₀
    rw [map_add, map_nsmul, toPic_pullCart, GlobalTheory.CechPic.pull_comp, mul_smul,
      ← map_nsmul (CechPic.pull t) a₀, e₀', map_add, smul_add, e₁, add_assoc]

end GlobalTheory.LogResBig
