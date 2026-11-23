import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsKernelEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemPolarizationStabilizerOfDualPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsKernelEqStatement

section
open NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.PolKerLie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PolKer
theorem polynomialKernel_constTerm_lieDeriv : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ Φ₁, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) →
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ₁) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM γ hγ Φ Φ₁ hΦ hd
  obtain ⟨T, hT, m, f, φ, hf, rfl, hz⟩ := hΦ
  have act := _root_.GlobalTheory.T.dualPair_preserves_polarization hP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.RealUniq.isPair_V hM.triple)
  obtain ⟨D, hDm, hDi⟩ := act.2.2.1 γ hγ
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
    intro i
    filter_upwards [T.finite_toSet.compl_mem_cofinite, hM.triple.geo.hM.std] with v hv hs
    rw [(hf i).2.2 v hv, hs]
  have hder : ∀ i x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (pure (f i) (φ i)) x)
      (pure (D (f i)) (φ i) x) 0 := fun i x =>
    (hDi (f i) (hf i).1 (D (f i))).2 rfl _
      (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hf i).2.1 (hstd i)) x
  have hsum : ∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (∑ i, pure (f i) (φ i)) x)
      (∑ i, pure (D (f i)) (φ i) x) 0 := by
    intro x
    have eq : (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (∑ i, pure (f i) (φ i)) x) =
        fun t : ℝ => ∑ i ∈ Finset.univ, om (1, γ (Multiplicative.ofAdd t)) (pure (f i) (φ i)) x := by
      funext t
      simp [map_sum, Finset.sum_apply]
    rw [eq]
    exact HasDerivAt.fun_sum (fun i _ => hder i x)
  have e1 : Φ₁ = ∑ i, pure (D (f i)) (φ i) := by
    funext x
    rw [Finset.sum_apply]
    exact (hd x).unique (hsum x)
  refine ⟨T, hT, m, fun i => D (f i), φ, fun i => ⟨hDm _ (hf i).1, (hf i).2⟩, e1, ?_⟩
  let π : G.M.Pol Bs.ψ Bs.emb →ₗ[ℂ] R.Pi := R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype
  have hπ : Function.Surjective π := fun y => by
    have : y ∈ (G.M.Pol Bs.ψ Bs.emb).map R.p := hM.real.quot.onto ▸ Submodule.mem_top
    obtain ⟨g, hg, e⟩ := Submodule.mem_map.1 this
    exact ⟨⟨g, hg⟩, e⟩
  have ker0 : ∀ g ∈ G.M.Pol Bs.ψ Bs.emb, R.p g = 0 → R.p (D g) = 0 := fun g hg h0 => by
    have := hM.real.lie γ hγ g hg 0 (zero_mem _) (D g) 0 ((hDi g hg _).2 rfl)
      (GlobalTheory.ThK.RealUniq.actsD_zero _) (by rw [h0, map_zero])
    rwa [map_zero] at this
  let A := GlobalTheory.ThK.RealUniq.induced π hπ (D.restrict hDm) (fun u hu => ker0 u.1 u.2 hu)
  have hA : ∀ i, R.p (D (f i)) = A (R.p (f i)) := fun i =>
    (GlobalTheory.ThK.RealUniq.induced_apply π hπ (D.restrict hDm) (fun u hu => ker0 u.1 u.2 hu) ⟨f i, (hf i).1⟩).symm
  have := congrArg (A.rTensor _) hz
  simpa [map_sum, hA] using this
end GlobalTheory.PolKerLie
end
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAlgebra_preserves_polynomialKernel : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ Φ₁, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) →
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ₁) := by
  first | exact @_root_.GlobalTheory.PolKerLie.polynomialKernel_constTerm_lieDeriv | exact _root_.GlobalTheory.PolKerLie.polynomialKernel_constTerm_lieDeriv | (intros; apply _root_.GlobalTheory.PolKerLie.polynomialKernel_constTerm_lieDeriv <;> assumption)
end
