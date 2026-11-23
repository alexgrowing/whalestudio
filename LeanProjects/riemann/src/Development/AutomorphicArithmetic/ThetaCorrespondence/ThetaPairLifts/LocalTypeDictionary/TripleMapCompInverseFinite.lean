import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilIntertwiningValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftSurjectiveTripleInvariants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteAdeleActsPlacewise
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilIntertwiningValueStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.TripleAssembly
variable {D : D7}
set_option maxHeartbeats 1000000 in
theorem triple_map_comp_inverse_finite : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
        (∀ g ∈ GfC W, ∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (g, 1) Φ) = GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ) ∧
          ∀ g ∈ GfC W₁, ∀ Φ ∈ algF ψ θ false A₁ B, GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (ωB (g, 1) Φ) = GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ := by
  intro hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have hL1 := _root_.GlobalTheory.T.triple_invariant_theta_surjective hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have hL2 := _root_.GlobalTheory.T.local_action_finite_places hPr D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hM.triple
  refine ⟨fun g hg Φ hΦ => ?_, fun g hg Φ hΦ => ?_⟩
  · have key : ∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
        om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W (1) h.JW g, 1) Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb ∧
        GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W (1) h.JW g, 1) Ψ) =
          GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ := by
      have hfin := GlobalTheory.T.archSupported_smul_conjugateUnitary_sub_one_eq_zero D W (1 : D.host.E) h.JW g hg
      intro Ψ hΨ
      induction hΨ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, φ, hf, hφ, hv, rfl⟩ := hx
        obtain ⟨φ', hφ', hv', hd, he⟩ := hL2.1 _ hfin f φ hφ hv
        rw [he]
        refine ⟨Submodule.subset_span ⟨f, φ', hf, hφ', hv', rfl⟩, ?_⟩
        unfold GlobalTheory.TripleAssembly.liftPure
        split_ifs with H
        · rw [H.choose_spec f φ' hφ' hv', H.choose_spec f φ hφ hv]
          congr 2
          funext v
          have := hM.fin.inv v (hd v)
          rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
          exact this
        · rfl
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add, map_add, map_add, hx.2, hy.2]
        exact ⟨Submodule.add_mem _ hx.1 hy.1, rfl⟩
      | smul c x _ hx =>
        rw [map_smul, map_smul, map_smul, hx.2]
        exact ⟨Submodule.smul_mem _ c hx.1, rfl⟩
    obtain ⟨Ψ, hΨ, rfl⟩ := hL1.1 Φ hΦ
    have hS := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V Γ.W Γ.M Bs.ψ Bs.emb hM.triple.geo.hM hΨ
    have e1 := hTA Ψ hS g 1
    rw [toUX_one] at e1
    refine (congrArg (⇑(GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf)) e1.symm).trans ?_
    obtain ⟨k1, k2⟩ := key Ψ hΨ
    unfold GlobalTheory.TripleAssembly.mapA
    unfold GlobalTheory.TripleAssembly.thetaLift
    split_ifs with H
    · rw [H.choose_spec _ k1, H.choose_spec _ hΨ, k2]
    · rfl
  · have key : ∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
        om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁ g, 1) Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb ∧
        GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) (om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁ g, 1) Ψ) =
          GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ := by
      have hfin := GlobalTheory.T.archSupported_smul_conjugateUnitary_sub_one_eq_zero D W₁ (-1 : D.host.E) h.JW₁ g hg
      intro Ψ hΨ
      induction hΨ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, φ, hf, hφ, hv, rfl⟩ := hx
        obtain ⟨φ', hφ', hv', hd, he⟩ := hL2.2 _ hfin f φ hφ hv
        rw [he]
        refine ⟨Submodule.subset_span ⟨f, φ', hf, hφ', hv', rfl⟩, ?_⟩
        unfold GlobalTheory.TripleAssembly.liftPure
        split_ifs with H
        · rw [H.choose_spec f φ' hφ' hv', H.choose_spec f φ hφ hv]
          congr 2
          funext v
          have := hM.fin.inv' v (hd v)
          rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
          exact this
        · rfl
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add, map_add, map_add, hx.2, hy.2]
        exact ⟨Submodule.add_mem _ hx.1 hy.1, rfl⟩
      | smul c x _ hx =>
        rw [map_smul, map_smul, map_smul, hx.2]
        exact ⟨Submodule.smul_mem _ c hx.1, rfl⟩
    obtain ⟨Ψ, hΨ, rfl⟩ := hL1.2 Φ hΦ
    have hS := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V' Γ.W Γ.M' Bs.ψ Bs.emb hM.triple.geo.hM' hΨ
    have e1 := hTB Ψ hS g 1
    rw [toUX_one] at e1
    refine (congrArg (⇑(GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf)) e1.symm).trans ?_
    obtain ⟨k1, k2⟩ := key Ψ hΨ
    unfold GlobalTheory.TripleAssembly.mapB
    unfold GlobalTheory.TripleAssembly.thetaLift
    split_ifs with H
    · rw [H.choose_spec _ k1, H.choose_spec _ hΨ, k2]
    · rfl
end GlobalTheory.TripleAssembly
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
theorem _root_.GlobalTheory.T.triple_assembly_inverse_finite : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
        (∀ g ∈ GfC W, ∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (g, 1) Φ) = GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ) ∧
          ∀ g ∈ GfC W₁, ∀ Φ ∈ algF ψ θ false A₁ B, GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (ωB (g, 1) Φ) = GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ := by
  first | exact @_root_.GlobalTheory.TripleAssembly.triple_map_comp_inverse_finite | exact _root_.GlobalTheory.TripleAssembly.triple_map_comp_inverse_finite | (intros; apply _root_.GlobalTheory.TripleAssembly.triple_map_comp_inverse_finite <;> assumption)
end
