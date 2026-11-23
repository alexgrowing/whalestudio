import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchDer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationPairDerivation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistPolarizationDatumLieDerivative
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.IsDatumDerivativeSecondFactorEqSumPure

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.LieEq
theorem polarization_match_lie_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ Φ₀' ∈ algF ψ θ false A₁ B, IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ' → IsDer θ X (fun h => ωB (1, h)) τ Y Φ₀ Φ₀' → ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ'D ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ Φ₀'D ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M ψ cA Φ'D Φ' → IsDatum Γ.M' ψ cB Φ₀D Φ₀ → IsDatum Γ.M' ψ cB Φ₀'D Φ₀' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD Φ₀D → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf Φ'D Φ₀'D := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ _ hO hTr R Rf hM Pi rf rl p p' _ τ Y hY
    Φ _ Φ' _ Φ₀ _ Φ₀' _ hD hD₀ ΦD _ Φ'D _ Φ₀D _ Φ₀'D _ hd1 hd2 hd3 hd4 hPM
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.T.exists_oneParamSubgroup_transposeGram_lieAt D θ X τ Y hθ hY e Γ.W hO.JX
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_lieDerivative_polynomialFock_seesaw Bs Γ Xc om om' hTr γ hγ
  obtain ⟨δ', hδ'⟩ := _root_.GlobalTheory.T.twist_lie_derivative_model hP Bs Γ Xc om om' hTr γ hγ
  obtain ⟨Aop, hA, hA'⟩ := exists_op (Γ.M.Pol Bs.ψ Bs.emb) (Γ.M'.Pol Bs.ψ Bs.emb) R.p R.p' δ δ'
    (fun f hf f' hf' hpp => hM.real.lie γ hγ f hf f' hf' _ _ (hδ f hf).2 (hδ' f' hf').2 hpp)
  obtain ⟨T, hT, m, m', f, φ, f', φ', hf, hf', hΦ, hΦ', hs⟩ := hPM
  have e1 := _root_.GlobalTheory.T.twist_polarization_datum_lie_derivative hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hTr τ Y γ hγt hγ Φ Φ' hD T m f
    (fun i => δ (f i)) φ hf (fun i => (hδ _ (hf i).1).2) (hΦ ▸ hd1) Φ'D hd2
  have e2 := _root_.GlobalTheory.T.twist_polarization_datum_derivative_second hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hTr τ Y γ hγt hγ Φ₀ Φ₀' hD₀ T m' f'
    (fun j => δ' (f' j)) φ' hf' (fun j => (hδ' _ (hf' j).1).2) (hΦ' ▸ hd3) Φ₀'D hd4
  refine ⟨T, hT, m, m', fun i => δ (f i), φ, fun j => δ' (f' j), φ', fun i => ⟨(hδ _ (hf i).1).1, (hf i).2⟩,
    fun j => ⟨(hδ' _ (hf' j).1).1, (hf' j).2⟩, e1, e2, ?_⟩
  have := congrArg (TensorProduct.map Aop LinearMap.id) hs
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply] at this
  simpa only [hA _ (hf _).1, hA' _ (hf' _).1] using this
end GlobalTheory.SquareAgree.LieEq
end
end
