import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.DegreeInfimum.PlaceDegreeSums
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.KerCorePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.LocalQuotientRank
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNumberFieldFunctionalBoundedCompExtensionStatement

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem ndeg_eq_places {K : Type} [Field K] [NumberField K] (N : MLine K) (hN : N.Good)
    (hc : ∀ σ : K →+* ℂ, N.n ((starRingEnd ℂ).comp σ) = N.n σ) :
    ((∑ᶠ w : HeightOneSpectrum (𝓞 K), (-(FractionalIdeal.count K w N.I : ℝ)) * logN w) -
      ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (N.n σ.embedding)) / (Module.finrank ℚ K : ℝ) = N.ndeg := by
  have h1 : (∑ᶠ w : HeightOneSpectrum (𝓞 K), (-(FractionalIdeal.count K w N.I : ℝ)) * logN w) =
      -Real.log ((FractionalIdeal.absNorm N.I : ℚ) : ℝ) := by
    simp_rw [neg_mul]
    rw [finsum_neg_distrib, PlaceDegreeSums.sum_count_log_norm _ hN.1]
  have h2 : ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (N.n σ.embedding) =
      ∑ τ : K →+* ℂ, Real.log (N.n τ) := by
    rw [PlaceDegreeSums.sum_infinite_places_mult (fun σ => Real.log (N.n σ.embedding))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rcases InfinitePlace.embedding_mk_eq τ with h | h
    · rw [h]
    · rw [h]
      exact congrArg Real.log (hc τ)
  rw [h1, h2, MLine.ndeg, MLine.deg]

theorem qbridge_of_numGood : ∀ (D : D7) (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Ch Ah Cc Ac Tt cc : ℝ) (be : HeightOneSpectrum (𝓞 B.KO) → ℝ) (Carch Bdeg : ℝ), Submodule.IsLattice B.KO (B.Mlat j ka) → (∀ la, 0 ≤ be la) → (Function.support be).Finite → (∑ᶠ la, be la * WeightFamilies.lnN B la) / WeightFamilies.degO B ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size → (∀ τ F, B.supN j ka ((starRingEnd ℂ).comp τ) F = B.supN j ka τ F) → WeightFamilies.PPv D large₂ Ch Ah * ka.size + Carch + Bdeg + Real.log (WeightFamilies.rhoP B CR Tt cc j ka : ℝ) / 2 ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size → (∀ F : B.Cusp j ka, F ∉ WeightFamilies.MggK B CR Tt cc j ka → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra B.KO K₁) (φ : B.Cusp j ka →ₗ[B.KO] K₁), WeightFamilies.MggK B CR Tt cc j ka ≤ LinearMap.ker φ ∧ φ F ≠ 0 ∧ NumGood (B.Mlat j ka : Set (B.Cusp j ka)) (B.supN j ka) be Carch Bdeg K₁ φ) → QBridgeAt large₂ B j ka CR Ch Ah Cc Ac Tt cc := by
  intro D large₂ B j ka CR Ch Ah Cc Ac Tt cc be Carch Bdeg hlat hbe hbefin hbesum hconj hroom hdet
  classical
  obtain ⟨K₁, _, _, _, ρ, g, cf, hfam, hcf, hker, hdim⟩ := kerCore_holds B.KO (B.Cusp j ka)
    (WeightFamilies.MggK B CR Tt cc j ka)
    (fun K₁ _ _ _ φ => WeightFamilies.MggK B CR Tt cc j ka ≤ LinearMap.ker φ ∧
      NumGood (B.Mlat j ka : Set (B.Cusp j ka)) (B.supN j ka) be Carch Bdeg K₁ φ)
    (fun _ _ _ _ _ h => h.1)
    (fun v hv => by
      by_contra hn
      obtain ⟨K₁, _, _, _, φ, h1, h2, h3⟩ := hdet v hn
      exact h2 (hv K₁ φ ⟨h1, h3⟩))
    (fun K' K₁ _ _ _ _ _ _ e f hf => ⟨e.toLinearMap.comp f, ⟨fun v hv => by
      have := LinearMap.mem_ker.1 (hf.1 hv)
      simp [LinearMap.mem_ker, this], GlobalTheory.T.isNumberFieldFunctionalBounded_comp_extension _ _ _ _ _ _ _ K' K₁ e f hf.2⟩, fun _ => rfl⟩)
  have hrk : WeightFamilies.rhoP B CR Tt cc j ka + Module.finrank B.KO (WeightFamilies.MggK B CR Tt cc j ka) =
      Module.finrank B.KO (B.Cusp j ka) :=
    LocalQuotientRank.rank_QuotMW (K := B.KO) (B.Mlat j ka) hlat.fg hlat.span_eq_top (WeightFamilies.MggK B CR Tt cc j ka)
  have hρ : ρ = WeightFamilies.rhoP B CR Tt cc j ka := by omega
  subst hρ
  choose N hG hd hc hint harch using fun i => (hfam i).2
  refine ⟨K₁, inferInstance, inferInstance, inferInstance, cf, be,
    fun i w => -(FractionalIdeal.count K₁ w (N i).I : ℝ), fun i σ => Real.log ((N i).n σ.embedding), Carch, Bdeg,
    hker, hbe, hbefin, hbesum, fun i => ?_, fun la w hw i F hF hne => ?_, hconj, fun σ i F hF hne => ?_,
    fun i => ?_, hroom⟩
  · refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (N i).I)).subset fun w hw h => hw ?_
    simp [h]
  · rw [hcf] at hne ⊢
    exact (hint i la w hw F hF hne).trans_eq (sub_eq_add_neg _ _)
  · rw [hcf] at hne ⊢
    rw [← InfinitePlace.norm_embedding_eq]
    exact harch i σ.embedding F hF hne
  · rw [ndeg_eq_places (N i) (hG i) (hc i)]
    exact hd i

end GlobalTheory.ArcCM
