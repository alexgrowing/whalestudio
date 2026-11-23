import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalCompactInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumFiniteDimensionalOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLinearInPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
noncomputable section

namespace GlobalTheory.ThKAutKInf

theorem mem_polData_of_polMatch {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {a a' : ℕ} (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a') (Φ Φ')
    (h : PolMatch B G X R Rf Φ Φ') : Φ ∈ GlobalTheory.ThK.PolData B G.M := by
  obtain ⟨T, -, m, m', f, φ, f', φ', hf, -, rfl, -, -⟩ := h
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (hf i).1, φ i, (hf i).2.1, ?_, rfl⟩
  refine Filter.eventually_cofinite.2 ((T.finite_toSet).subset fun v hv => ?_)
  by_contra hvT
  exact hv ((hf i).2.2 v hvT)

theorem isAut_thetaIntegral_of_le_kInf : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c →
      ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' →
      ∀ K : Subgroup (GAd σ (c • G.W.J.map σ)), (∀ x ∈ K, (toGAd hσ G.W.J hc).symm x ∈ KInf σ G.W B.emb) →
        IsAut σ (c • G.W.J.map σ) K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hσ c hc hcs Φ Φ' _hΦ' hPM K hK
  have hT := hM.triple
  have hΦ := mem_polData_of_polMatch B G X R Rf Φ Φ' hPM
  obtain ⟨K₀, -, hA⟩ := GlobalTheory.T.exists_maximal_compact_invariant F E σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ
  refine ⟨hA.mod, ?_, hA.zfin⟩
  obtain ⟨S, hSf, hSle, hS⟩ := GlobalTheory.T.polynomial_datum_finite_dimensional_orbit F E σ B _ _ G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hKP
    (GlobalTheory.ThK.Inhab.pairV hT) Φ hΦ
  obtain ⟨L, hL⟩ := GlobalTheory.T.theta_integral_linear_in_polynomial F E σ B a a' G X om om' hKP hT
  let P := GlobalTheory.ThK.PolData B G.M
  let S' : Submodule ℂ P := S.comap P.subtype
  haveI : FiniteDimensional ℂ S := hSf
  haveI : FiniteDimensional ℂ S' :=
    FiniteDimensional.of_injective (K := ℂ) (V₂ := S) ((P.subtype.domRestrict S').codRestrict S fun x => x.2)
      fun x y e => Subtype.ext (Subtype.ext (congrArg (fun z : S => (z : GlobalTheory.ThK.Fn F a (a + a'))) e))
  let T : P →ₗ[ℂ] (GAd σ (c • G.W.J.map σ) → ℂ) :=
    LinearMap.funLeft ℂ ℂ (toGAd hσ G.W.J hc).symm ∘ₗ L
  refine Submodule.finiteDimensional_of_le (S₂ := S'.map T) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  have hk := hS _ (hK k k.2)
  refine ⟨⟨om (1, (toGAd hσ G.W.J hc).symm k) Φ, hSle hk⟩, hk, ?_⟩
  funext g
  simp only [T, LinearMap.coe_comp, Function.comp_apply, LinearMap.funLeft_apply, hL, map_mul]
  unfold Model.I theta
  congr 1
  funext x
  rw [show ((x, (toGAd hσ G.W.J hc).symm g * (toGAd hσ G.W.J hc).symm k) : UA σ G.V.J × UA σ G.W.J) =
    (x, (toGAd hσ G.W.J hc).symm g) * (1, (toGAd hσ G.W.J hc).symm k) by simp, map_mul, Module.End.mul_apply]

end GlobalTheory.ThKAutKInf
