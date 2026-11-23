import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SignatureAndNodeGaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfIndexEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain

namespace GlobalTheory.Chain.InnerSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem theta_pureTensorO {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P) := by
  refine (GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) 1 (fun k f hf => ⟨?_, rfl⟩) f hf P).1
  obtain ⟨τ, i, j⟩ := k
  exact GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_sub (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ _ hf)
    (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ _ hf)))

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem ptY_and_ItY_of_pair (hP : ItPair D) (hC : ∀ k, ChainPar D k) (hθ : IsInfFam R.θ) (hω : R.chain_ωY)
    (hS : ∀ t (k : Fin D.R.m), (k : ℕ) + 1 < D.R.m → IsStepWeil k R.ψ (Yc D k) (Yc D (k + 1)) (R.ωY t k) ∧
      IsVacVec R.ψ R.θ (R.MY k) (R.MY (k + 1)) (R.vY t k)) :
    R.chain_ptY ∧ ∃ It, ({ R with ItY := It } : RealDat D A Ks).chain_ItY := by
  classical
  refine ⟨fun t k hk P => theta_pureTensorO (hω t k hk).std hθ _ _ _ _ (hS t ⟨k, by omega⟩ hk).2.theta P, ?_⟩
  have h : ∀ k, k + 1 < D.R.m → ∃ y, ∀ t, IsItW R.θ (R.MY k) (R.MY (k + 1)) (R.ωY t k) (R.ptY t k) y := by
    intro k hk
    have hk0 : k < D.R.m := by omega
    obtain ⟨It, h⟩ := exists_intertwiner_of_index_eq hP ⟨k, hk0⟩ (hC _) (Yc D k) (Yc D (k + 1))
      (min k D.R.m) (min (k + 1) D.R.m) (min_eq_left hk0.le) (min_eq_left hk.le)
      (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ
    exact ⟨It, fun t => h _ _ (hS t ⟨k, hk0⟩ hk).1 (hS t ⟨k, hk0⟩ hk).2⟩
  refine ⟨fun k => if hk : k + 1 < D.R.m then (h k hk).choose else 0, fun t k hk => ?_⟩
  show IsItW R.θ (R.MY k) (R.MY (k + 1)) (R.ωY t k) (R.ptY t k) (if hk : k + 1 < D.R.m then (h k hk).choose else 0)
  rw [dif_pos hk]
  exact (h k hk).choose_spec t

end GlobalTheory.Chain.InnerSteps

end
