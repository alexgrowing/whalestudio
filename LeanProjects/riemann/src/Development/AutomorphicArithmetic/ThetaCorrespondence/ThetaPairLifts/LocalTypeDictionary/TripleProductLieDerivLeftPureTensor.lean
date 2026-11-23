import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilDoublingValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftSurjectiveTripleInvariants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationPairDerivation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLineDerivative
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilDoublingValueStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.TripleAssembly
set_option maxHeartbeats 1000000 in
theorem exists_pure_tensor_lieDeriv_left_factor : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
      ∀ τ, ∀ Y ∈ lieAt X τ, ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W,
        (∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X e h.JX (oneP θ X τ Y t)) →
        ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' →
        ∃ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
          (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
          (∀ i, f i ∈ Γ.M.Pol Bs.ψ Bs.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ i v = Γ.M.vac v) ∧
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) ∧
          (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb ∧
          Φ = GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∧
          Φ' = GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) := by
  intro hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm τ Y hY γ hγ hγt
    Φ hΦ Φ' hΦ' hD
  classical
  have hg := hm.triple.geo
  have hψ' : Bs.ψ = ψ := h.ψ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ' ▸ hm.triple.base.std
  have hG : Γ.M.IsGood ψ := hψ' ▸ hg.hM
  obtain ⟨Ψ, hΨ, rfl⟩ := (_root_.GlobalTheory.T.triple_invariant_theta_surjective hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB
    R Rf hm).1 Φ hΦ
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.1 hΨ
  choose f0 φ hf0 hφ hvac hpure using fun i => (g i).2
  let f : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)) := fun i => c i • f0 i
  have hΨeq : Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpure i]
    funext x
    simp only [Pi.smul_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, f, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]
  subst hΨeq
  have hfP : ∀ i, f i ∈ Γ.M.Pol Bs.ψ Bs.emb := fun i => Submodule.smul_mem _ _ (hf0 i)
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.DerPol.polarization_pair_derivation hP Γ.M Bs.ψ Bs.emb Xc.β (Xc.β / Xc.α) om hm.triple.base.cm hm.triple.base.std
    hm.triple.weil γ hγ
  refine ⟨n, f, fun i => δ (f i), φ, fun i => ⟨hfP i, hφ i, hvac i, (hδ _ (hfP i)).2⟩,
    Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨δ (f i), φ i, (hδ _ (hfP i)).1, hφ i, hvac i, rfl⟩, rfl, ?_⟩
  have hstdi : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers D.host.F} 1 := by
    intro i
    filter_upwards [hg.hM.std, hvac i] with v hv hv'
    rw [hv', hv]
  have hrest : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑(f i)) (GlobalTheory.EvZeroInf.finPart (φ i)) :=
    fun i => ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, by
      rw [← GlobalTheory.EvZeroInf.pure_eq_tens]; exact GlobalTheory.TensUniq.pure_mem_schA _ _ (hφ i) (hstdi i)⟩
  have hsum' : ∀ k : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
      ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (k i) (φ i) =
        ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑(k i)) (GlobalTheory.EvZeroInf.finPart (φ i)) := fun k =>
    Finset.sum_congr rfl fun i _ => GlobalTheory.EvZeroInf.pure_eq_tens _ _
  have hmem : ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) ∈ GlobalTheory.WeilM.schA D.host.F _ :=
    Submodule.sum_mem _ fun i _ => GlobalTheory.TensUniq.pure_mem_schA _ _ (hφ i) (hstdi i)
  have hone : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW 1 = 1 := by
    apply Subtype.ext; simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]
  funext x
  have h1 : HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho ψ (GlobalTheory.TripleRead.ptO (sgn true W).gram e x)
      (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i))))) (Φ' x) 0 := by
    refine (hD x).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    have h3 := tA _ hmem 1 (oneP θ X τ Y t)
    rw [hone, ← hγt t] at h3
    exact congrFun h3 x
  have h4 := _root_.GlobalTheory.T.twisted_theta_line_derivative hP Bs Γ Xc om om' hm.triple γ hγ n f (fun i => δ (f i)) (fun i => GlobalTheory.EvZeroInf.finPart (φ i))
    hrest (fun i => (hδ _ (hfP i)).2) (GlobalTheory.TripleRead.ptO (sgn true W).gram e x)
  rw [← hsum', ← hsum', hψ'] at h4
  exact (h4.unique h1).symm
end GlobalTheory.TripleAssembly
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tripleProduct_lieDeriv_left_pure_tensor : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
      ∀ τ, ∀ Y ∈ lieAt X τ, ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W,
        (∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X e h.JX (oneP θ X τ Y t)) →
        ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' →
        ∃ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
          (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
          (∀ i, f i ∈ Γ.M.Pol Bs.ψ Bs.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ i v = Γ.M.vac v) ∧
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) ∧
          (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb ∧
          Φ = GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∧
          Φ' = GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) := by
  first | exact @_root_.GlobalTheory.TripleAssembly.exists_pure_tensor_lieDeriv_left_factor | exact _root_.GlobalTheory.TripleAssembly.exists_pure_tensor_lieDeriv_left_factor | (intros; apply _root_.GlobalTheory.TripleAssembly.exists_pure_tensor_lieDeriv_left_factor <;> assumption)
end
