import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingLocalFactor
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumDifferentiableAlongLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingLocalFactorStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.SquareAgree.LieDat
theorem isDatum_derivative_second_factor_eq_sum_pure : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (γ : Multiplicative ℝ →* UA D.sp.cm.sig Γ.W.J),
    (∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hO.JX (oneP θ X τ Y t)) → γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W →
    ∀ (Φ Φ' : WO W₁ X → ℂ), IsDer θ X (fun h => ωB (1, h)) τ Y Φ Φ' →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F)) (m : ℕ) (f f₁ : Fin m → SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
    (∀ i, f i ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ v ∉ T, φ i v = Γ.M'.vac v) →
    (∀ i, ActsD (evI D.host.F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    IsDatum Γ.M' ψ cB (∑ i, pure (f i) (φ i)) Φ →
    ∀ Φ'D, IsDatum Γ.M' ψ cB Φ'D Φ' → Φ'D = ∑ i, pure (f₁ i) (φ i) := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hT τ Y γ hγ hL Φ Φ' hDer T m f f₁ φ hf hact hD Φ'D hΦ'D
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  have hM : Γ.M'.IsGood ψ := hO.psi ▸ hT.geo.hM'
  have hW : Γ.M'.IsWeil ψ Xc.α (Xc.α / Xc.β) om' := hO.psi ▸ hT.weil'
  have hev : ∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = Γ.M'.vac v := fun i =>
    ⟨(hf i).2.1, Filter.eventually_cofinite.2 ((T.finite_toSet).subset fun v hv => by
      by_contra h; exact hv ((hf i).2.2 v h))⟩
  have hval : ∀ (t : ℝ) u, GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho ψ u (om' (1, γ (Multiplicative.ofAdd t)) (∑ i, pure (f i) (φ i)))) =
      ωB (1, oneP θ X τ Y t) Φ (cB u) := by
    intro t u
    have h := (hO.weilB _ Φ hD 1 (oneP θ X τ Y t)).2 u
    rwa [GlobalTheory.LocWeilAct.conjU_one', ← hγ t] at h
  have hnew : IsDatum Γ.M' ψ cB (∑ i, pure (f₁ i) (φ i)) Φ' := by
    refine ⟨Submodule.sum_mem _ fun i _ => GlobalTheory.TensUniq.pure_mem_schA (f₁ i) (φ i) (hev i).1
      (((hev i).2.and hM.std).mono fun v hv => hv.1.trans hv.2), fun u => ?_⟩
    have h1 := _root_.GlobalTheory.T.theta_sum_differentiable_along_line hP Γ.M' ψ Xc.α (Xc.α / Xc.β) om' hT.base.cm hstd hM hW γ hL m f f₁ φ hev hact u
    have h2 : HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho ψ u (om' (1, γ (Multiplicative.ofAdd t)) (∑ i, pure (f i) (φ i))))) (Φ' (cB u)) 0 := by
      simp only [hval]
      exact hDer (cB u)
    exact h1.unique h2
  exact GlobalTheory.T.schwartzDatum_eq_of_thetaFunction_eq Γ.M' ψ hstd cB Φ'D _ Φ' hΦ'D hnew
end GlobalTheory.SquareAgree.LieDat
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_polarization_datum_derivative_second : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (γ : Multiplicative ℝ →* UA D.sp.cm.sig Γ.W.J),
    (∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hO.JX (oneP θ X τ Y t)) → γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W →
    ∀ (Φ Φ' : WO W₁ X → ℂ), IsDer θ X (fun h => ωB (1, h)) τ Y Φ Φ' →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F)) (m : ℕ) (f f₁ : Fin m → SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
    (∀ i, f i ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ v ∉ T, φ i v = Γ.M'.vac v) →
    (∀ i, ActsD (evI D.host.F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    IsDatum Γ.M' ψ cB (∑ i, pure (f i) (φ i)) Φ →
    ∀ Φ'D, IsDatum Γ.M' ψ cB Φ'D Φ' → Φ'D = ∑ i, pure (f₁ i) (φ i) := by
  first | exact @_root_.GlobalTheory.SquareAgree.LieDat.isDatum_derivative_second_factor_eq_sum_pure | exact _root_.GlobalTheory.SquareAgree.LieDat.isDatum_derivative_second_factor_eq_sum_pure | (intros; apply _root_.GlobalTheory.SquareAgree.LieDat.isDatum_derivative_second_factor_eq_sum_pure <;> assumption)
end
