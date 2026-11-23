import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatFinitePlaceCompletionLeAleph0Statement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankAlgebraicDataSchrodingerModelLeAleph0Statement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankPolynomialFockSchrodingerModelLeAleph0Statement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

theorem GlobalTheory.SquareAgree.rank_pi_le_aleph0 : GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
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
    Module.rank ℂ Pi ≤ Cardinal.aleph0 := by
  intro _ _ _ D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _ _ hO hT R Rf _ Pm rf rl p p' hm
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  let S := GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank))
  let T : S →ₗ[ℂ] (WO W X → ℂ) :=
    { toFun := fun Φ x => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho ψ (cA.symm x) Φ.1)
      map_add' := fun Φ Ψ => funext fun x => by
        have e : Γ.M.co.rho ψ (cA.symm x) (Φ.1 + Ψ.1) = Γ.M.co.rho ψ (cA.symm x) Φ.1 + Γ.M.co.rho ψ (cA.symm x) Ψ.1 := by
          funext z; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply]; ring
        simp only [Submodule.coe_add, Pi.add_apply, e]
        exact GlobalTheory.WeilM.thetaSum_add _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M ψ hstd _ _ Φ.2) (GlobalTheory.HeisSchA.rho_mem_schA Γ.M ψ hstd _ _ Ψ.2)
      map_smul' := fun c Φ => funext fun x => by
        have e : Γ.M.co.rho ψ (cA.symm x) (c • Φ.1) = c • Γ.M.co.rho ψ (cA.symm x) Φ.1 := by
          funext z; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]; ring
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, e]
        exact GlobalTheory.WeilM.thetaSum_smul _ c _ }
  let Q := (algD Γ.M Bs.ψ Bs.emb).comap S.subtype
  have hle : algF ψ θ true A B ≤ Q.map T := by
    intro Φ hΦ
    obtain ⟨ΦD, hD, hDat⟩ := hO.algA Φ hΦ
    refine ⟨⟨ΦD, hDat.1⟩, hD, funext fun x => ?_⟩
    have := hDat.2 (cA.symm x)
    rw [AddEquiv.apply_symm_apply] at this
    exact this
  have hQ : Module.rank ℂ Q ≤ Module.rank ℂ (algD Γ.M Bs.ψ Bs.emb) := by
    rw [(Submodule.equivMapOfInjective S.subtype Subtype.val_injective Q).rank_eq]
    exact Submodule.rank_mono (Submodule.map_comap_le _ _)
  have hD : Module.rank ℂ (algD Γ.M Bs.ψ Bs.emb) ≤ Cardinal.aleph0 :=
    GlobalTheory.T.rank_algebraicData_schrodingerModel_le_aleph0 Γ.M Bs.ψ Bs.emb hT.geo.hM (GlobalTheory.T.rank_polynomialFock_schrodingerModel_le_aleph0 Bs Γ.M hT.base hT.geo.hV hT.geo.hW hT.geo.hM) (fun v => GlobalTheory.T.rank_schwartzBruhat_finitePlaceCompletion_le_aleph0 v _)
  calc Module.rank ℂ Pm = Module.rank ℂ (⊤ : Submodule ℂ Pm) := (rank_top ℂ Pm).symm
    _ = Module.rank ℂ ((algF ψ θ true A B).map p) := by rw [hm.mapA.onto]
    _ ≤ Module.rank ℂ (algF ψ θ true A B) := rank_map_le _ _
    _ ≤ Module.rank ℂ (Q.map T) := Submodule.rank_mono hle
    _ ≤ Module.rank ℂ Q := rank_map_le _ _
    _ ≤ _ := hQ.trans hD
