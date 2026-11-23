import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawFramesWeilEquivalenceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockAlgebraicThetaVectorsStableFiniteAdelesLieStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanOneParamLineTransposeGramUnitarStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealLieOperatorThetaQuotientLineStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilDoublingValueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaIdentityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaFactorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaArchimedeanStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem GlobalTheory.TripleAssembly.mapA_mapB_lieEquiv : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ →
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
        (∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' →
            GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ' = GlobalTheory.TripleAssembly.opLie θ ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) τ Y (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
          ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ false A₁ B, ∀ Φ' ∈ algF ψ θ false A₁ B, IsDer θ X (fun g => ωB (1, g)) τ Y Φ Φ' →
            GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ' = GlobalTheory.TripleAssembly.opLie θ ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) τ Y (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ) := by
  intro hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have key : ∀ τ, ∀ Y ∈ lieAt X τ, ∃ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf),
      (∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' →
        GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ' = T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
      (∀ Φ ∈ algF ψ θ false A₁ B, ∀ Φ' ∈ algF ψ θ false A₁ B, IsDer θ X (fun g => ωB (1, g)) τ Y Φ Φ' →
        GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ' = T (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ)) := by
    intro τ Y hY
    obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.T.exists_archimedean_one_param_line_transposeGramUnitary D θ hθ X e Γ.W h.JX τ Y hY
    obtain ⟨Ti, hTi, hTi'⟩ := GlobalTheory.T.exists_real_lie_operator_theta_quotient_line Bs Γ Xc om om' R Rf hM γ hγ
    refine ⟨LinearMap.rTensor _ Ti, ?_, ?_⟩
    · intro Φ hΦ Φ' hΦ' hD
      obtain ⟨m, f, f₁, φ, hf, hsum, rfl, rfl⟩ := GlobalTheory.T.seesaw_weil_doubling_value hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM τ Y hY γ hγ hγt Φ hΦ Φ' hΦ' hD
      have hmem : (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb :=
        Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, φ i, (hf i).1, (hf i).2.1, (hf i).2.2.1, rfl⟩
      have hφ : ∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = Γ.M.vac v :=
        fun i => ⟨(hf i).2.1, (hf i).2.2.1⟩
      rw [GlobalTheory.T.seesaw_weil_zeta_factor hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM m f₁ φ hφ hsum, GlobalTheory.T.seesaw_weil_zeta_factor hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM m f φ hφ hmem, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.rTensor_tmul, ← hTi _ (hf i).1 _ (hf i).2.2.2]
    · intro Φ hΦ Φ' hΦ' hD
      obtain ⟨m, f, f₁, φ, hf, hsum, rfl, rfl⟩ := GlobalTheory.T.seesaw_weil_zeta_identity hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM τ Y hY γ hγ hγt Φ hΦ Φ' hΦ' hD
      have hmem : (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb :=
        Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, φ i, (hf i).1, (hf i).2.1, (hf i).2.2.1, rfl⟩
      have hφ : ∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = Γ.M'.vac v :=
        fun i => ⟨(hf i).2.1, (hf i).2.2.1⟩
      rw [GlobalTheory.T.seesaw_weil_zeta_archimedean hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM m f₁ φ hφ hsum, GlobalTheory.T.seesaw_weil_zeta_archimedean hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM m f φ hφ hmem, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.rTensor_tmul, ← hTi' _ (hf i).1 _ (hf i).2.2.2]
  have H : ∀ τ, ∀ Y ∈ lieAt X τ, ∃ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf),
      ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' →
        GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ' = T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ) :=
    fun τ Y hY => let ⟨T, hA, _⟩ := key τ Y hY; ⟨T, hA⟩
  have hOp : ∀ τ, ∀ (Y) (hY : Y ∈ lieAt X τ),
      GlobalTheory.TripleAssembly.opLie θ ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) τ Y = (H τ Y hY).choose := by
    intro τ Y hY
    unfold GlobalTheory.TripleAssembly.opLie
    rw [dif_pos (H τ Y hY)]
  refine ⟨fun τ Y hY Φ hΦ Φ' hΦ' hD => ?_, fun τ Y hY Φ hΦ Φ' hΦ' hD => ?_⟩
  · rw [hOp τ Y hY]
    exact (H τ Y hY).choose_spec Φ hΦ Φ' hΦ' hD
  · have k := key τ Y hY
    have hA := k.choose_spec.1
    have hB := k.choose_spec.2
    have hst : ∀ Φ ∈ algF ψ θ true A B, ∃ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' :=
      (GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D ψ θ hψ hθ true W X A B β (β / α) ωA hWA).2.2 τ Y hY
    have hon : (algF ψ θ true A B).map (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) = ⊤ := (GlobalTheory.T.algF_map_mapA_and_mapB_eq_top hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM).1
    have hEq : (H τ Y hY).choose = k.choose := by
      apply LinearMap.ext
      intro x
      have hx : ∃ Ψ, Ψ ∈ algF ψ θ true A B ∧ GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Ψ = x :=
        (Submodule.mem_map (f := GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) (p := algF ψ θ true A B)).1
          ((Submodule.eq_top_iff'.1 hon) x)
      have hΨ := hx.choose_spec.1
      have h1 := (hst _ hΨ).choose_spec
      rw [← hx.choose_spec.2]
      exact ((H τ Y hY).choose_spec _ hΨ _ h1.1 h1.2).symm.trans (hA _ hΨ _ h1.1 h1.2)
    exact (hB Φ hΦ Φ' hΦ' hD).trans (congrArg (fun T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf) =>
      T (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ)) ((hOp τ Y hY).trans hEq).symm)
