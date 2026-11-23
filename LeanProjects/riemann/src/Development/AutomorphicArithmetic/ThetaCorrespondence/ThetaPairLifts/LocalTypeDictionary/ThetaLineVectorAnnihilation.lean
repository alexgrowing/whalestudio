import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingSwap
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LineDerivativeSplitEqSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingSwapStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.LineKillV
theorem line_vector_annihilated : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.V, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D ∈ algD Γ.M Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) (Φ₁D x) 0) → ∀ Φ₁,
    IsDatum Γ.M ψ cA Φ₁D Φ₁ → p Φ₁ = 0 := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTr Pi rf rl p p' hm γ hγ ΦD hΦD
    Φ₁D hΦ₁D hder Φ₁ hΦ₁
  have hψ : Bs.ψ = ψ := hO.psi
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ ▸ hTr.base.std
  obtain ⟨Y, γs, hY, hγs, hγsY, hprod⟩ := GlobalTheory.T.unitaryArchimedeanOneParam_eq_prod_cmType_lines D θ hθ W Γ.V hO.JW γ hγ
  obtain ⟨Ψ, hΨ, hΨd, hsum⟩ := _root_.GlobalTheory.T.line_derivative_splits hP _ _ _ Bs _ _ _ _ Γ.M _ _ om _ _ _ _
    (GlobalTheory.ThK.RealUniq.isPair_V hTr) _ γs hγs γ hγ hprod ΦD hΦD Φ₁D hder
  obtain ⟨Φ, hΦalg, hΦ⟩ := hO.algA' ΦD hΦD
  choose Φ' hΦ'alg hΦ' using fun τ => hO.algA' (Ψ τ) (hΨ τ)
  have hder' : ∀ τ, IsDer θ W (fun g => ωA (g, 1)) τ (Y τ) Φ (Φ' τ) := by
    intro τ z
    obtain ⟨u, rfl⟩ := cA.surjective z
    have h1 := hΨd τ u
    have e1 : (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ u (om (γs τ (Multiplicative.ofAdd t), 1) ΦD))) =
        fun t : ℝ => ωA (oneP θ W τ (Y τ) t, 1) Φ (cA u) := by
      funext t
      have h2 := (hO.weilA ΦD Φ hΦ (oneP θ W τ (Y τ) t) 1).2 u
      rw [GlobalTheory.KapXLine.kapX_one, ← hγsY τ t] at h2
      rw [hψ]; exact h2
    have e2 : GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ u (Ψ τ)) = Φ' τ (cA u) := by
      rw [hψ]; exact (hΦ' τ).2 u
    rw [e1, e2] at h1
    exact h1
  have hp : ∀ τ, p (Φ' τ) = 0 := fun τ =>
    hm.mapA.invl τ (Y τ) (hY τ) Φ hΦalg (Φ' τ) (hΦ'alg τ) (hder' τ)
  have hsumD : IsDatum Γ.M ψ cA Φ₁D (((Finset.univ : Finset D.what₂.Tau).toList.map Φ').sum) := by
    rw [hsum]; exact isDatum_list_sum hstd _ Ψ Φ' hΦ'
  rw [IsDatum.fun_eq Γ.M ψ cA cA.surjective hΦ₁ hsumD, map_list_sum, List.map_map]
  exact List.sum_eq_zero fun x hx => by
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact hp τ
end GlobalTheory.LineKillV
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_line_vector_annihilation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.V, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D ∈ algD Γ.M Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) (Φ₁D x) 0) → ∀ Φ₁,
    IsDatum Γ.M ψ cA Φ₁D Φ₁ → p Φ₁ = 0 := by
  first | exact @_root_.GlobalTheory.LineKillV.line_vector_annihilated | exact _root_.GlobalTheory.LineKillV.line_vector_annihilated | (intros; apply _root_.GlobalTheory.LineKillV.line_vector_annihilated <;> assumption)
end
