import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumPureMemAlgD

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKerCpt

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem pure_sub {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f g : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f - g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, sub_mul]

theorem kInf_rel_polZero : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.V Bs.emb, ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (k, 1) Φ - Φ) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM k hk Φ hΦ
  obtain ⟨D, hDP, hD⟩ := (GlobalTheory.T.polynomial_datum_action_of_pair hP F E σ Bs a (a + a') G.V G.W G.M Xc.β (Xc.β / Xc.α) om _ _ _ _
    (GlobalTheory.ThK.RealUniq.isPair_V hM.triple)).2.1 k hk
  obtain ⟨n, c, g, rfl⟩ := (Submodule.mem_span_set').1 hΦ
  choose f φ hf hSB hcof hg using fun i => (g i).2
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x : Fin a × Fin (a + a') → Fv F v | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
    intro i
    filter_upwards [hcof i, hM.triple.geo.hM.std] with v h1 h2
    rw [h1, h2]
  have hmem : ∀ i, c i • f i ∈ G.M.Pol Bs.ψ Bs.emb := fun i => Submodule.smul_mem _ _ (hf i)
  have key : ∀ i, om (k, 1) (pure (c i • f i) (φ i)) = pure (D (c i • f i)) (φ i) := fun i =>
    (hD _ (hmem i) _).2 rfl _ (GlobalTheory.ThK.EvUniqInf.rest_pure _ _ (hSB i) (hstd i))
  have hp : ∀ i, R.p (D (c i • f i) - c i • f i) = 0 := fun i => by
    rw [map_sub, hM.real.quot.cpt k hk _ (hmem i) _ ((hD _ (hmem i) _).2 rfl), sub_self]
  classical
  let S : Fin n → Finset (Pl F) := fun i => (Filter.eventually_cofinite.1 (hcof i)).toFinset
  refine ⟨Xc.T ∪ Finset.univ.biUnion S, Finset.subset_union_left, n, fun i => D (c i • f i) - c i • f i, φ,
    fun i => ⟨Submodule.sub_mem _ (hDP _ (hmem i)) (hmem i), hSB i, fun v hv => ?_⟩, ?_, ?_⟩
  · by_contra h
    exact hv (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, by simpa [S] using h⟩))
  · have e : ∀ i, c i • (g i : (Fin a × Fin (a + a') → AF F) → ℂ) = pure (c i • f i) (φ i) := fun i => by
      rw [hg i, GlobalTheory.PolMatchLin.pure_smul]
    simp only [e, map_sum, key, pure_sub, Finset.sum_sub_distrib]
  · simp only [hp, TensorProduct.zero_tmul, Finset.sum_const_zero]

end GlobalTheory.PolKerCpt
