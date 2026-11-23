import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsKernelIntegral
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemPolarizationStabilizerOfDualPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsKernelIntegralStatement

section
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace GlobalTheory.PolKerLieV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
local notation "pureT" => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
theorem polynomialKernel_constTerm_lieDeriv_dualSpace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.V, ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, ∀ Φ₁,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ₁) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM γ hγ Φ hΦ Φ₁ hd
  classical
  obtain ⟨T, m, f, φ, hfφ, rfl⟩ := exists_decomp G.M Bs.ψ Bs.emb hΦ
  obtain ⟨D, hDmem, hD⟩ := (_root_.GlobalTheory.T.dualPair_preserves_polarization hP F E σ Bs _ _ G.V G.W G.M _ _ om _ _ _ _
    (GlobalTheory.ThK.RealUniq.isPair_V hM.triple)).1 γ hγ
  have hstd := hM.triple.geo.hM.std
  have hacts : ∀ i, ActsD (evI F) (fun t => ⇑(om (γ (Multiplicative.ofAdd t), 1))) ⇑(f i) ⇑(D (f i)) :=
    fun i => (hD (f i) (hfφ i).1 (D (f i))).2 rfl
  have hrest : ∀ i, Rest (evI F) ⇑(f i) (GlobalTheory.EvZeroInf.finPart (φ i)) := by
    intro i
    refine GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hfφ i).2.1 ?_
    filter_upwards [hstd, (Filter.eventually_cofinite.2 (by simpa using T.finite_toSet) : ∀ᶠ v in Filter.cofinite, v ∉ T)] with v hv hvT
    rw [(hfφ i).2.2 v hvT, hv]
  have hpure : ∀ i x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) (pureT (f i) (φ i)) x)
      (pureT (D (f i)) (φ i) x) 0 := by
    intro i x
    rw [GlobalTheory.EvZeroInf.pure_eq_tens, GlobalTheory.EvZeroInf.pure_eq_tens]
    exact hacts i _ (hrest i) x
  have hsum : ∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) (∑ i, pureT (f i) (φ i)) x)
      (∑ i, pureT (D (f i)) (φ i) x) 0 := by
    intro x
    refine (HasDerivAt.sum (u := Finset.univ) (fun i _ => hpure i x)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => ?_)
    simp [map_sum, Finset.sum_apply]
  have hΦ₁ : Φ₁ = ∑ i, pureT (D (f i)) (φ i) := by
    funext x
    rw [Finset.sum_apply]
    exact (hd x).unique (hsum x)
  have hp0 : ∀ i, R.p (D (f i)) = 0 := fun i =>
    hM.real.quot.lie γ hγ (f i) (hfφ i).1 (D (f i)) (hacts i)
  refine ⟨T ∪ Xc.T, Finset.subset_union_right, m, fun i => D (f i), φ, fun i =>
    ⟨hDmem _ (hfφ i).1, (hfφ i).2.1, fun v hv => (hfφ i).2.2 v (fun h => hv (Finset.mem_union_left _ h))⟩,
    hΦ₁, ?_⟩
  simp [hp0]
end GlobalTheory.PolKerLieV
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAlgebra_preserves_polynomialKernel_dualSpace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.V, ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, ∀ Φ₁,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ₁) := by
  first | exact @_root_.GlobalTheory.PolKerLieV.polynomialKernel_constTerm_lieDeriv_dualSpace | exact _root_.GlobalTheory.PolKerLieV.polynomialKernel_constTerm_lieDeriv_dualSpace | (intros; apply _root_.GlobalTheory.PolKerLieV.polynomialKernel_constTerm_lieDeriv_dualSpace <;> assumption)
end
