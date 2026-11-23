import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaResidue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaImageEqSpanDarboux
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaResidueStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.TripleAssembly.Transport
end GlobalTheory.TripleAssembly.Transport
open GlobalTheory.TripleAssembly.Transport in
theorem GlobalTheory.TripleAssembly.triple_twist_transport_eq : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
        ((∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
            GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ) =
              GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ) ∧
          ∀ Φ ∈ algF ψ θ true A B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ = Φ) ∧
        ((∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
            GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ) =
              GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ) ∧
          ∀ Φ ∈ algF ψ θ false A₁ B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ = Φ) := by
  intro hHowe hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h htA htB R Rf hM
  have hgood : Γ.M.IsGood ψ := h.ψ ▸ hM.triple.geo.hM
  have hgood' : Γ.M'.IsGood ψ := h.ψ ▸ hM.triple.geo.hM'
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := h.ψ ▸ hM.triple.base.std
  have hZ : Γ.W.J.det ≠ 0 := by
    rw [h.JX, Matrix.det_smul, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit X).ne_zero
  have hY : Γ.V.J.det ≠ 0 := by
    rw [h.JW, one_smul]; exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W).ne_zero
  have hY' : Γ.V'.J.det ≠ 0 := by
    rw [h.JW₁, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W₁).ne_zero
  obtain ⟨T₁, hT₁, hi₁⟩ := GlobalTheory.ThetaTransformInj.linear_injective D Γ.M ψ (sgn true W).gram e hgood hstd hY hZ
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (sgn true W)).ne_zero
  obtain ⟨T₂, hT₂, hi₂⟩ := GlobalTheory.ThetaTransformInj.linear_injective D Γ.M' ψ (sgn false W₁).gram e hgood' hstd hY' hZ
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (sgn false W₁)).ne_zero
  have hle := GlobalTheory.TripleAssembly.darbAlg_le_schA _ _ _ Γ.M Bs.ψ Bs.emb hM.triple.geo.hM
  have hle' := GlobalTheory.TripleAssembly.darbAlg_le_schA _ _ _ Γ.M' Bs.ψ Bs.emb hM.triple.geo.hM'
  obtain ⟨hI, hI'⟩ := _root_.GlobalTheory.T.theta_image_eq_span_darboux hHowe hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h htA htB R Rf hM
  have ex1 := exists_factor T₁ _ (fun Φ hΦ => hi₁ Φ (hle hΦ))
    (GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf))
  have ex2 := exists_factor T₂ _ (fun Φ hΦ => hi₂ Φ (hle' hΦ))
    (GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf))
  refine ⟨⟨fun Ψ hΨ => ?_, fun Φ hΦ => ?_⟩, ⟨fun Ψ hΨ => ?_, fun Φ hΦ => ?_⟩⟩
  · have H : ∃ q : (Matrix (Fin X.rank) (Fin W.rank) (AE D) → ℂ) →ₗ[ℂ] _, ∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
        q (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ) =
          GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ := by
      obtain ⟨q, hq⟩ := ex1
      exact ⟨q, fun Ψ hΨ => by rw [← hT₁ Ψ (hle hΨ)]; exact hq Ψ hΨ⟩
    unfold GlobalTheory.TripleAssembly.mapA GlobalTheory.TripleAssembly.thetaLift
    rw [dif_pos H]
    exact H.choose_spec Ψ hΨ
  · rw [← hI T₁ hT₁] at hΦ
    obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.1 hΦ
    exact ⟨Ψ, hΨ, (hT₁ Ψ (hle hΨ)).symm⟩
  · have H : ∃ q : (Matrix (Fin X.rank) (Fin W₁.rank) (AE D) → ℂ) →ₗ[ℂ] _, ∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
        q (GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ) =
          GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ := by
      obtain ⟨q, hq⟩ := ex2
      exact ⟨q, fun Ψ hΨ => by rw [← hT₂ Ψ (hle' hΨ)]; exact hq Ψ hΨ⟩
    unfold GlobalTheory.TripleAssembly.mapB GlobalTheory.TripleAssembly.thetaLift
    rw [dif_pos H]
    exact H.choose_spec Ψ hΨ
  · rw [← hI' T₂ hT₂] at hΦ
    obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.1 hΦ
    exact ⟨Ψ, hΨ, (hT₂ Ψ (hle' hΨ)).symm⟩
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
theorem _root_.GlobalTheory.T.triple_twist_transport : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
        ((∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
            GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ) =
              GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ) ∧
          ∀ Φ ∈ algF ψ θ true A B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ = Φ) ∧
        ((∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
            GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ) =
              GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ) ∧
          ∀ Φ ∈ algF ψ θ false A₁ B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ = Φ) := by
  first | exact @_root_.GlobalTheory.TripleAssembly.triple_twist_transport_eq | exact _root_.GlobalTheory.TripleAssembly.triple_twist_transport_eq | (intros; apply _root_.GlobalTheory.TripleAssembly.triple_twist_transport_eq <;> assumption)
end
