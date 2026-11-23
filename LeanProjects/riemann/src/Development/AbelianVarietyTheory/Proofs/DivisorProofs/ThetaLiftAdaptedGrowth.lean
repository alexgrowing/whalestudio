import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFunctionBoundedOnUnipotentStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.DescB.CTAdd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem span_contInv {n : ℕ} {W : Spc F E n} (S : Set (UA σ W.J → ℂ))
    (hS : ∀ f ∈ S, Continuous f ∧ ∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h) :
    ∀ f ∈ Submodule.span ℂ S, Continuous f ∧ ∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf => exact hS f hf
  | zero => exact ⟨continuous_const, fun _ _ _ => rfl⟩
  | add f g _ _ ihf ihg =>
    refine ⟨ihf.1.add ihg.1, fun γ hγ h => ?_⟩
    simp only [Pi.add_apply, ihf.2 γ hγ h, ihg.2 γ hγ h]
  | smul r f _ ihf =>
    refine ⟨ihf.1.const_smul r, fun γ hγ h => ?_⟩
    simp only [Pi.smul_apply, ihf.2 γ hγ h]

end GlobalTheory.ThK.DescB.CTAdd

open GlobalTheory.ThK.DescB.CTAdd in
set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.ThK.DescB.isCT_add_thetaSpan : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ →
      ∀ f ∈ thetaSpanV B G X om R Rf, ∀ g ∈ thetaSpanV' B G X om' R Rf, ∀ c d : UA σ G.W.J → ℂ,
        IsCT H' f c → IsCT H' g d → IsCT H' (f + g) (c + d) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM d₁ W₁ H' i₀ i₁ hH' f hf g hg c d hc hd μ 𝓕 hμ hF h1 h
  have hT := hM.triple

  have hPol : ∀ Φ Φ', PolMatch B G X R Rf Φ Φ' → Φ ∈ PolData B G.M ∧ Φ' ∈ PolData B G.M' := by
    intro Φ Φ' hPM
    obtain ⟨T, -, m, m', f, φ, f', φ', hf, hf', e1, e2, -⟩ := hPM
    refine ⟨e1 ▸ Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_,
      e2 ▸ Submodule.sum_mem _ fun j _ => Submodule.subset_span ?_⟩
    · exact ⟨f i, (hf i).1, φ i, (hf i).2.1,
        Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by_contra fun hT => hv ((hf i).2.2 v hT)), rfl⟩
    · exact ⟨f' j, (hf' j).1, φ' j, (hf' j).2.1,
        Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by_contra fun hT => hv ((hf' j).2.2 v hT)), rfl⟩
  have hfC := span_contInv _ (by
    rintro _ ⟨Φ, Φ', hΦ', hPM, rfl⟩
    exact GlobalTheory.T.continuous_left_invariant_theta hK F E σ B a a' G X om om' hT Φ (hPol Φ Φ' hPM).1) f hf
  have hgC := span_contInv _ (by
    rintro _ ⟨Φ, Φ', hΦ', hPM, rfl⟩
    exact GlobalTheory.T.continuous_left_invariant_dual hK F E σ B a a' G X om om' hT Φ' ⟨(hPol Φ Φ' hPM).2, hΦ'⟩) g hg
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hfin : μ 𝓕 ≠ ⊤ := by rw [h1]; exact ENNReal.one_ne_top
  have hint : ∀ k : UA σ G.W.J → ℂ, Continuous k → (∀ γ ∈ ratU σ G.W.J, ∀ h, k (γ * h) = k h) →
      IntegrableOn (fun u : unip σ G.W H' => k (u.1 * h)) 𝓕 μ := by
    intro k hk hki
    obtain ⟨C, hC⟩ := GlobalTheory.T.automorphic_function_bounded_on_unipotent F E σ B (a + a') d₁ G.W W₁ H' i₀ i₁ _ _ hT.base hT.geo.hW hH' k hk hki h
    exact Measure.integrableOn_of_bounded (M := C) hfin
      (hk.comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable
      (ae_of_all _ fun u => hC u.1 u.2)
  have e1 := hc μ 𝓕 hμ hF h1 h
  have e2 := hd μ 𝓕 hμ hF h1 h
  show c h + d h = ∫ u in 𝓕, (f (u.1 * h) + g (u.1 * h)) ∂μ
  rw [integral_add (hint f hfC.1 hfC.2) (hint g hgC.1 hgC.2), ← e1, ← e2]
