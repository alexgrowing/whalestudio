import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DarbouxModelAlgebraicVectorsLeAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleInv

theorem theta_surj : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ →
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
        (∀ Φ ∈ algF ψ θ true A B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ = Φ) ∧
          ∀ Φ ∈ algF ψ θ false A₁ B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ = Φ := by
  intro hHowe hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTr hTr' R Rf hM
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := h.ψ ▸ hM.triple.base.std
  have hG : Γ.M.IsGood ψ := h.ψ ▸ hM.triple.geo.hM
  have hG' : Γ.M'.IsGood ψ := h.ψ ▸ hM.triple.geo.hM'
  have hX : Γ.W.J.det ≠ 0 := by
    rw [h.JX, Matrix.det_smul, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)) (gram_det_ne X)
  have hV : Γ.V.J.det ≠ 0 := by
    rw [h.JW, one_smul]; exact gram_det_ne W
  have hV' : Γ.V'.J.det ≠ 0 := by
    rw [h.JW₁, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (gram_det_ne W₁)
  obtain ⟨hmain, hmain'⟩ := GlobalTheory.T.seesaw_weil_factorization hHowe hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTr hTr' R Rf hM
  refine ⟨?_, ?_⟩
  · obtain ⟨T, hT1, -⟩ := GlobalTheory.T.thetaTransform_darbouxModel_linear_injective D Γ.M ψ (sgn true W).gram e hG hstd hV hX (gram_det_ne _)
    intro Φ hΦ
    rw [← hmain T hT1] at hΦ
    obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.1 hΦ
    refine ⟨Ψ, hΨ, (hT1 Ψ ?_).symm⟩
    exact GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V Γ.W Γ.M Bs.ψ Bs.emb hM.triple.geo.hM hΨ
  · obtain ⟨T, hT1, -⟩ := GlobalTheory.T.thetaTransform_darbouxModel_linear_injective D Γ.M' ψ (sgn false W₁).gram e hG' hstd hV' hX (gram_det_ne _)
    intro Φ hΦ
    rw [← hmain' T hT1] at hΦ
    obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.1 hΦ
    refine ⟨Ψ, hΨ, (hT1 Ψ ?_).symm⟩
    exact GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V' Γ.W Γ.M' Bs.ψ Bs.emb hM.triple.geo.hM' hΨ

end GlobalTheory.TripleInv
