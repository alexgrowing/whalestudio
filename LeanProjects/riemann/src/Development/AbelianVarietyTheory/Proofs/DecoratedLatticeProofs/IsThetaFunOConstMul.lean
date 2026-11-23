import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsRamNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroupStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastSeeSaw

variable {D : D7}

theorem isThetaFunO_const_mul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (fun w => c * f w) where
  quasi γ w := by
    show c * f (ratW T S γ + w) = _ * (c * f w)
    rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hU, hk⟩ := hf.level
    refine ⟨U, hU, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (hk u hu h0) w
    simp only [heisO] at e ⊢
    rw [← e]; ring
  cont := continuous_const.mul hf.cont
  smooth n L hL h0 w := contDiff_const.mul (hf.smooth n L hL h0 w)

theorem isThetaFunO_kap {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ ⬝ (L.gram ⬝ τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ}
    {f : WO L S → ℂ} (hf : IsThetaFunO ψ L S f) : IsThetaFunO ψ S L'' (fun w => f (kap τ S w)) := by
  obtain ⟨hadd, hcont, hrat, -, hsym, hpart⟩ := GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1) (by simpa using hτ)
    (kap τ S) (fun _ => rfl)
  have hsH : ∀ x y, symplOH L S (kap τ S x) (kap τ S y) = symplOH S L'' x y := fun x y => by
    simp only [symplOH, hsym]; push_cast; ring
  let K : WO S L'' →+ WO L S := AddMonoidHom.mk' (kap τ S) hadd
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp hcont, fun n M hM h0 w => ?_⟩
  · obtain ⟨γ', hγ'⟩ := hrat (ratW L'' S γ) (by rw [ratW_eq]; exact rat_mem _)
    show f (kap τ S (ratW L'' S γ + w)) = _
    have e : ratW S L γ' = kap τ S (ratW L'' S γ) := hγ'
    rw [hadd, ← e, hf.quasi, e, hsH]
  · obtain ⟨U, hU, hk⟩ := hf.level
    refine ⟨U.comap K, hU.preimage hcont, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (hk (kap τ S u) hu ((hpart u).1 h0)) (kap τ S w)
    simp only [heisO] at e ⊢
    rw [hadd, ← hsH]
    exact e
  · have := hf.smooth n (K.comp M) (hcont.comp hM) (fun t => (hpart (M t)).2 (h0 t)) (kap τ S w)
    simp only [hadd]
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply, K] using this

end GlobalTheory.LastSeeSaw
end

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LastSeeSaw

end GlobalTheory.LastSeeSaw
end
