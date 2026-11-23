import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantThetaMeanSquareForm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
noncomputable section
namespace GlobalTheory.ThetaMeanSquareF
theorem exists_invariant_form_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ M : Submodule ℂ (WOF F E nS nT → ℂ), (∀ f ∈ M, IsThetaFunOF σ JS JT ξ₀ B.ψ f) →
      ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ →
        ∃ Bf : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ (u : WOF F E nS nT) (f g f' g' : M),
          (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ u f → (g' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ u g →
            Bf f' g' = Bf f g) ∧
          ∀ f : M, ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (Bf f f).re := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ M hM μ 𝓕 hμ h𝓕
  have hψ : IsCharAF F B.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hB.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := countable_of_discrete_addSubgroup _
  haveI := hμ
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc μ h𝓕⟩
  have hb : ∀ f ∈ M, ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C := fun f hf => by
    have hp : ∀ γ ∈ ratLF F E nS nT, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm ((hM f hf).quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul])
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hM f hf).cont.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  obtain ⟨Bf, hBf, hN⟩ := GlobalTheory.ThetaMeanSquareForm.exists_form (μ.restrict 𝓕) M
    (fun f hf => (hM f hf).cont.measurable) hb
  refine ⟨Bf, fun u f g f' g' hf hg => ?_, hN⟩
  rw [hBf, hBf, hf, hg]
  have key := GlobalTheory.HeisOrtho.setIntegral_add_right (G := WOF F E nS nT) (ratLF F E nS nT) μ 𝓕 h𝓕
    (fun w => (f : WOF F E nS nT → ℂ) w * (starRingEnd ℂ) ((g : WOF F E nS nT → ℂ) w)) (by
      rintro _ ⟨γ, rfl⟩ w
      have h0 := GlobalTheory.HeisOrtho.mul_conj_of_norm_one (hψ.2.1 (-(symplOHF σ JS JT ξ₀ (ratWF γ) w)))
      have h1 := (hM f f.2).quasi γ w
      have h2 := (hM g g.2).quasi γ w
      show (f : WOF F E nS nT → ℂ) (ratWF γ + w) * (starRingEnd ℂ) ((g : WOF F E nS nT → ℂ) (ratWF γ + w)) = _
      rw [h1, h2, map_mul, mul_mul_mul_comm, h0, one_mul]) u
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  have h0 := GlobalTheory.HeisOrtho.mul_conj_of_norm_one (hψ.2.1 (symplOHF σ JS JT ξ₀ w u))
  show B.ψ (symplOHF σ JS JT ξ₀ w u) * (f : WOF F E nS nT → ℂ) (w + u) *
    (starRingEnd ℂ) (B.ψ (symplOHF σ JS JT ξ₀ w u) * (g : WOF F E nS nT → ℂ) (w + u)) = _
  rw [map_mul, mul_mul_mul_comm, h0, one_mul]
end GlobalTheory.ThetaMeanSquareF
end
end
