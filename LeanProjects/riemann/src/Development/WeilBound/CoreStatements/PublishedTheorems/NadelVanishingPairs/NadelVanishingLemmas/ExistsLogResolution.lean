import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsSmoothProjectiveModel
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsEmbeddedResolutionStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.LogResExist

theorem exists_logRes : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X), η ≠ 0 → ∀ Z : Closeds X, Z ≠ ⊤ → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (s : Y ⟶ X) (_ : IsDominant s) (K : CartierDiv Y) (B : Closeds Y), IsLogRes p n η m G s K B ∧ ∀ y, s y ∈ Z → y ∈ B := by
  intro hP k _ _ X _ p n hp hdim η m G hη Z hZ
  obtain ⟨Y₀, hY₀, s₀, hs₀, hsm, hproj, hbij⟩ := GlobalTheory.T.exists_smooth_projective_birational_model hP k X p n hp hdim
  let Z₀ : Closeds Y₀ := ⟨s₀.base ⁻¹' (Z : Set X), Z.isClosed.preimage s₀.base.hom.continuous⟩
  have hZ₀ : Z₀ ≠ ⊤ := by
    intro h
    apply hZ
    have hsub : Set.range s₀.base ⊆ (Z : Set X) := by
      rintro _ ⟨y, rfl⟩
      have : y ∈ (Z₀ : Set Y₀) := by rw [h]; trivial
      exact this
    have hcl : closure (Set.range s₀.base) ⊆ (Z : Set X) := closure_minimal hsub Z.isClosed
    rw [s₀.denseRange.closure_range] at hcl
    ext x
    simp only [Closeds.coe_top, Set.mem_univ, iff_true]
    exact hcl trivial
  obtain ⟨-, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hproj
  obtain ⟨Y, hY, t, ht, K, B, hres, hB, -⟩ :=
    GlobalTheory.T.exists_embedded_resolution hP k X p n η m G hη Y₀ s₀ hsm hproj hbij Z₀ hZ₀ A hA
  haveI := ht
  exact ⟨Y, hY, t ≫ s₀, inferInstance, K, B, hres, fun y hy => hB y (by simpa [Z₀] using hy)⟩

end GlobalTheory.LogResExist
