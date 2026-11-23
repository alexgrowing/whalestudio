import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAllTiedEqTiedOnOfRealised
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilTiedEqOfEqTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameChrOfChrEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionLevelDataOfEqualTuplesZeroIntertwinersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakCompatibilityOfRealRowSideAdelicChainStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaRecordTrue

theorem recFun_of_rows (hR : GlobalTheory.Published.CuspRapidDecay) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (what₂ : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch)
    (hio : ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0) :
    ∀ θ : InfF (w.D Z), IsInfFam θ → ∀ ψ, IsStdChar (w.D Z) ψ (-1) → ∀ Wf : WeilFun (w.D Z) ψ,
      ∃ Rc : RecFun (w.D Z) θ ψ, Rc.ChrIs (TC.cf w.I w.l Z) n.tp.xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ}, ∀ j, j ≤ (w.D Z).R.m → ∀ x y : (w.D Z).what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt ((w.D Z).sp.Y j) (Rc.mY μ j * Rc.petC ((w.D Z).sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y) := by
  intro θ hθ ψ hψ Wf
  letI : Algebra what₂.r.z.core.Q.c.F (w.D Z).what₂.LL := what₂.r.z.alg
  have h3 := Formalism.IndefR.Links.RealDat3.characterisation_of_weak what₂.r.z.pins.char what₂.exAt
  have hC : what₂.r.z.R.toRealDat.C = TC.cf w.I w.l Z := what₂.r.z.lev.C
  obtain ⟨Rc, h1, h2, h4⟩ := GlobalTheory.T.functionLevelData_of_equal_tuples_zero_intertwiners hR (w.D Z) _ _ _ _ _ what₂.r.z.R.toRealDat h3.lev h3.models h3.chain n.tp.xi
    {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ} what₂.r.Y.tupT n.tp.xi_fin n.tp.xi_triv
    (fun μ hμ => ⟨by
        rw [what₂.r.z.lev.xiH, ← what₂.r.tup_ix, what₂.r.Y.tupTie μ hμ, ← n.xi]; rfl,
      GlobalTheory.T.weakCompatibility_of_realRowSide_adelicChain (w.D Z) _ _ _ _ _ what₂.r.z.R.toRealDat what₂.r.z.F.lv2 what₂.r.Y.tupT what₂.r.Y.hm what₂.r.Y.hTop what₂.r.Y.Ish _
        (w.D Z).what₂.onb (w.D Z).what₂.ft h3.models h3.chain what₂.r.Y.tied.sharp μ hμ⟩)
    (fun μ hμ => hio μ hμ) θ hθ ψ hψ Wf
  rw [hC] at h1
  exact ⟨Rc, h1, h2, h4⟩

set_option maxHeartbeats 1000000 in

theorem thEx_main : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) → ∀ 𝒮 : Slots, (∀ K B f T (w : ColW B f T) (Z : w.Lt) Wt p0 (t : RowsT K w Z Wt p0), 𝒮.Rx K B f T w Z Wt p0 t → ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0) → ThEx 𝒮 := by
  intro hW hR _ _ hDS hDSu hDSR 𝒮 hio
  refine StepW.of_all fun K B f T w _ _ _ Z l => ?_
  obtain ⟨X, hio', -, A, a, heq, hchr⟩ := GlobalTheory.Mem.Th.exists_allTied_eqTied_on hW hR hDS hDSu hDSR (w.D Z) (TC.cf w.I w.l Z) l.n.tp.xi
    {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ} l.real (recFun_of_rows hR l.what₂ l.n (hio K B f T w Z l.Wt l.p0 l.what₂ l.rx))
  obtain ⟨H, hH⟩ := hchr l.nch l.n.tp rfl
  exact ⟨X, ⟨⟨A, a, GlobalTheory.Mem.Th.weilTiedEq_of_eqTied _ _ _ _ heq, H,
    GlobalTheory.SameChrFin.sameChr_of_chrEq _ _ _ _ _ _ _ hH, a.W.ψ_std, hio'⟩⟩⟩

end GlobalTheory.ThetaRecordTrue

end
