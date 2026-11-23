import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingLocalIntegral
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.AlgDAndPreimageStableUnderKInf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumDifferentiableAlongLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingLocalIntegralStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
namespace GlobalTheory.SquareAgree.KerCptW
theorem ker_projection_maximalCompact_stable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.W Bs.emb, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ Φ₁,
    IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M ψ cA (om (1, k) ΦD) Φ₁ → p Φ = 0 → p Φ₁ = 0 := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ _ hO hTr Pi rf rl p p' hm k hk ΦD hΦD Φ Φ₁
    hD hD1 hp
  have hψ := hO.psi
  subst hψ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd Bs.ψ := hTr.base.std
  let Fn : ((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) → WO W X → ℂ :=
    fun Ψ z => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ (cA.symm z) Ψ)
  have hFn : ∀ Ψ f, IsDatum Γ.M Bs.ψ cA Ψ f → f = Fn Ψ := by
    intro Ψ f h
    funext z
    have h1 := h.2 (cA.symm z)
    rw [AddEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hex : ∀ Ψ ∈ algD Γ.M Bs.ψ Bs.emb, IsDatum Γ.M Bs.ψ cA Ψ (Fn Ψ) ∧ Fn Ψ ∈ algF Bs.ψ θ true A B := by
    intro Ψ hΨ
    obtain ⟨f, hf, hd⟩ := hO.algA' Ψ hΨ
    obtain rfl := hFn _ _ hd
    exact ⟨hd, hf⟩
  let q₀ : (algD Γ.M Bs.ψ Bs.emb) →ₗ[ℂ] Pi :=
    { toFun := fun Ψ => p (Fn Ψ.1)
      map_add' := fun Ψ₁ Ψ₂ => by
        have h := CoinvPass.isDatum_add hstd (hex _ Ψ₁.2).1 (hex _ Ψ₂.2).1
        show p (Fn (Ψ₁.1 + Ψ₂.1)) = _
        rw [← hFn _ _ h, map_add]
      map_smul' := fun c Ψ => by
        have h := CoinvPass.isDatum_smul c (hex _ Ψ.2).1
        show p (Fn (c • Ψ.1)) = _
        rw [← hFn _ _ h, map_smul]
        rfl }
  obtain ⟨Q, hQ⟩ := q₀.exists_extend
  have hQv : ∀ Ψ (h : Ψ ∈ algD Γ.M Bs.ψ Bs.emb), Q Ψ = p (Fn Ψ) := fun Ψ h => LinearMap.congr_fun hQ ⟨Ψ, h⟩
  have key := _root_.GlobalTheory.T.algD_and_preimage_stable_under_KInf hP Bs Γ.M Xc.β (Xc.β / Xc.α) om hTr.base hTr.geo.hV hTr.geo.hW hTr.geo.hM hTr.weil Q ⊥ ?hyp k hk ΦD hΦD
  · obtain ⟨hmem, hker⟩ := key
    have h0 : Q ΦD ∈ (⊥ : Submodule ℂ Pi) := by
      rw [Submodule.mem_bot, hQv _ hΦD, ← hFn _ _ hD, hp]
    have h2 := hker h0
    rw [Submodule.mem_bot, hQv _ hmem, ← hFn _ _ hD1] at h2
    exact h2
  case hyp =>
    intro w Z γ hγ hw hw' m f f₁ φ hφ hf hact hN
    have hmemS : ∀ g : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F _, (∀ i, g i ∈ Γ.M.Pol Bs.ψ Bs.emb) →
        ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g i) (φ i) ∈ algD Γ.M Bs.ψ Bs.emb := fun g hg =>
      Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨g i, φ i, hg i, (hφ i).1, (hφ i).2, rfl⟩
    have hΨ := hmemS f fun i => (hf i).1
    have hΨ' := hmemS f₁ fun i => (hf i).2
    obtain ⟨τ, Y, hY, hγY⟩ := GlobalTheory.T.exists_lieGenerator_of_oneParameterSubgroup_realPlace D θ X hθ e Γ.W hO.JX Bs.emb w Z γ hγ hw hw'
    have hder : IsDer θ X (fun h => ωA (1, h)) τ Y (Fn (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))
        (Fn (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i))) := by
      intro z
      have hd := _root_.GlobalTheory.T.theta_sum_differentiable_along_line hP Γ.M Bs.ψ _ _ om hTr.base.cm hstd hTr.geo.hM hTr.weil γ hγ m f f₁ φ hφ hact (cA.symm z)
      refine hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      have hw1 := hO.weilA _ _ (hex _ hΨ).1 1 (oneP θ X τ Y t)
      rw [GlobalTheory.LocWeilAct.conjU_one' W 1 hO.JW, ← hγY t] at hw1
      have := hFn _ _ hw1
      show ωA (1, oneP θ X τ Y t) (Fn _) z = _
      rw [this]
    have hpe := hm.mapA.eql τ Y hY _ (hex _ hΨ).2 _ (hex _ hΨ').2 hder
    rw [Submodule.mem_bot] at hN ⊢
    rw [hQv _ hΨ'] at ⊢
    rw [hQv _ hΨ] at hN
    rw [hpe, hN, map_zero]
end GlobalTheory.SquareAgree.KerCptW
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
theorem _root_.GlobalTheory.T.square_agree_kernel_compact_stable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.W Bs.emb, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ Φ₁,
    IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M ψ cA (om (1, k) ΦD) Φ₁ → p Φ = 0 → p Φ₁ = 0 := by
  first | exact @_root_.GlobalTheory.SquareAgree.KerCptW.ker_projection_maximalCompact_stable | exact _root_.GlobalTheory.SquareAgree.KerCptW.ker_projection_maximalCompact_stable | (intros; apply _root_.GlobalTheory.SquareAgree.KerCptW.ker_projection_maximalCompact_stable <;> assumption)
end
