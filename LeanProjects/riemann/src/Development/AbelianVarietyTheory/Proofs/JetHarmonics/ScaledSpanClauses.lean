import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaScaledSpanLeSigmaSmulUnscaledSpanStatement
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory

theorem scaledSpan_clauses : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J) (z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (act : P → B.Cusp j ka → B.Cusp j ka), FormTie X hinj EX p ka wL wF T O v i z act → WeightAlgebra.IsF' ka wL wF T wF.n → ka.n = wF.n + T * wL.n → WeightFamilies.dimY D j ≤ T → WeightAlgebra.H2 X (scalOfP B hinj EX p ka wL wF T) ka wL wF → (∀ g F, X.inc ka F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T → X.inc ka (act g F) ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T) → O.Th v i ≤ O.Ms i ∧ (∀ g : P, (O.Th v i).map ((O.ρ i g).restrictScalars (𝓞 K)) ≤ O.Th v i) ∧ O.σ v i ≠ 0 ∧ O.Th v i ≤ Formalism.EigenvalueLevelCeiling.sc (O.σ v i) (O.ThK v i) := by
  intro D B P6 j X hinj EX p ka wL wF T K _ _ _ _ Bs Df S P _ _ oc O v i z act h hF hn hD h2 hact
  obtain ⟨hσ, hsig⟩ := GlobalTheory.T.theta_scaled_span_le_sigma_smul_unscaled_span D B P6 j X hinj EX p ka wL wF T hF hn hD
  have hle := Formalism.MainNotions.Gaps.T0.theta_le_msup X _ h2 hF rfl hn hD
  have hσK : (((sigRec B hinj EX ka wL wF T : 𝓞 B.KO) : B.KO)) ≠ 0 := by
    intro h0
    exact hσ (RingOfIntegers.coe_eq_zero_iff.1 h0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h.Th_eq, h.Ms_eq]
    refine Submodule.span_mono (Set.image_mono fun F hFm => ?_)
    obtain ⟨G, hG, e⟩ := Submodule.mem_map.1 (hle hFm)
    have : G = F := X.inc_inj ka e
    exact this ▸ hG
  · intro g
    rw [h.Th_eq, spanK, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨F, hFm, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨act g F, hact g F hFm, ?_⟩
    exact (h.rho_eq g F).symm
  · rw [h.σ_eq]
    exact (map_ne_zero_iff _ (algebraMap B.KO K).injective).2 hσK
  · rw [h.Th_eq, spanK, Submodule.span_le]
    rintro _ ⟨F, hFm, rfl⟩
    obtain ⟨G, hG, e⟩ := hsig _ hFm
    set s : B.KO := ((sigRec B hinj EX ka wL wF T : 𝓞 B.KO) : B.KO) with hs
    have e' : X.inc ka F = s • G := by
      rw [e, hs]
      exact (algebraMap_smul B.KO _ G).symm
    have hG' : X.inc ka (s⁻¹ • F) = G := by
      rw [map_smul, e', smul_smul, inv_mul_cancel₀ hσK, one_smul]
    have hmem : z.symm (1 ⊗ₜ[B.KO] (s⁻¹ • F)) ∈ O.ThK v i :=
      h.ThK_ge (Submodule.subset_span ⟨s⁻¹ • F, by simpa [hG'] using hG, rfl⟩)
    refine Submodule.mem_map.2 ⟨_, hmem, ?_⟩
    have key : O.σ v i • z.symm (1 ⊗ₜ[B.KO] (s⁻¹ • F)) = z.symm (1 ⊗ₜ[B.KO] F) := by
      rw [← map_smul, h.σ_eq]
      congr 1
      change algebraMap B.KO K s • _ = _
      rw [algebraMap_smul, ← TensorProduct.tmul_smul, smul_smul, mul_inv_cancel₀ hσK, one_smul]
    simpa using key

end GlobalTheory
