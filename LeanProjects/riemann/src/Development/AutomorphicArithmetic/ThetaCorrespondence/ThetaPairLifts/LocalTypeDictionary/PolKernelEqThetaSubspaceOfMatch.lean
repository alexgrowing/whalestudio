import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsTripleFactor
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationKernelCompactVanishing
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LieAlgebraPreservesPolynomialKernel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MaximalCompactFixedRelPolynomialKernelConstTerm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LieAlgebraPreservesPolynomialKernelDualSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsTripleFactorStatement

section
open NumberField IsDedekindDomain
open scoped TensorProduct
theorem GlobalTheory.PolKer.polKernel_eq_thetaSubspace_of_match : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∃ K, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) K ∧
      K ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb ∧
      ∀ ΦD ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, (ΦD ∈ K ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' _ R Rf hM
  have hiff := GlobalTheory.T.polynomialMatch_zero_iff_pureTensor_image_zero F E σ Bs a a' G Xc om om' R Rf hM
  obtain ⟨h00, hlin⟩ := GlobalTheory.PolMatchLin.polMatch_linear Bs G Xc om om' R Rf hM.fin
  let K : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) :=
    { carrier := {Φ | Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf Φ 0}
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, by
        simpa using hlin x y 0 0 1 hx.2 hy.2⟩
      zero_mem' := ⟨zero_mem _, h00⟩
      smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, by
        simpa using hlin 0 x 0 0 c h00 hx.2⟩ }
  have memK : ∀ Φ, Φ ∈ K ↔ GlobalTheory.PolKer.PolZero Bs G Xc R Rf Φ := fun Φ =>
    ⟨fun h => (hiff Φ).1 h.2, fun h => ⟨GlobalTheory.PolKer.algD_of_polZero Bs G Xc R Rf Φ h, (hiff Φ).2 h⟩⟩
  have one_W : ∀ v, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v) := by
    intro v u _; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat]
  refine ⟨K, ⟨⟨fun Φ h => h.1, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro v h hh Φ hΦ
    exact (memK _).2 (GlobalTheory.T.finitePlace_unitaryPoint_keeps_zeroMatchedData F E σ Bs a a' G Xc om om' R Rf hM v h hh Φ ((memK Φ).1 hΦ))
  · intro k hk Φ hΦ
    exact (memK _).2 (_root_.GlobalTheory.T.polarization_kernel_compact_vanishing hP F E σ Bs a a' G Xc om om' R Rf hM k hk Φ ((memK Φ).1 hΦ))
  · intro γ hγ Φ hΦ Φ₁ _ hd
    exact (memK _).2 (_root_.GlobalTheory.T.lieAlgebra_preserves_polynomialKernel hP F E σ Bs a a' G Xc om om' R Rf hM γ hγ Φ Φ₁ ((memK Φ).1 hΦ) hd)
  · intro v g hg Φ hΦ
    exact (memK _).2 (GlobalTheory.T.algebraicData_unitaryRelations_finitePlace_polZero F E σ Bs a a' G Xc om om' R Rf hM v g hg Φ hΦ)
  · intro k hk Φ hΦ
    exact (memK _).2 (_root_.GlobalTheory.T.maximalCompact_invariants_polynomialKernel hP F E σ Bs a a' G Xc om om' R Rf hM k hk Φ hΦ)
  · intro γ hγ Φ hΦ Φ₁ _ hd
    exact (memK _).2 (_root_.GlobalTheory.T.lieAlgebra_preserves_polynomialKernel_dualSpace hP F E σ Bs a a' G Xc om om' R Rf hM γ hγ Φ hΦ Φ₁ hd)
  · intro hK
    obtain ⟨Φ, hΦ, hn⟩ := GlobalTheory.T.exists_algebraicDatum_not_matched_zero F E σ Bs a a' G Xc om om' R Rf hM
    rw [← hK] at hΦ
    exact hn ((memK Φ).1 hΦ)
  · intro ΦD hΦD
    exact ⟨fun h => h.2, fun h => ⟨hΦD, h⟩⟩
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSubspace_contains_polKernel : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∃ K, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) K ∧
      K ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb ∧
      ∀ ΦD ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, (ΦD ∈ K ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0) := by
  first | exact @_root_.GlobalTheory.PolKer.polKernel_eq_thetaSubspace_of_match | exact _root_.GlobalTheory.PolKer.polKernel_eq_thetaSubspace_of_match | (intros; apply _root_.GlobalTheory.PolKer.polKernel_eq_thetaSubspace_of_match <;> assumption)
end
