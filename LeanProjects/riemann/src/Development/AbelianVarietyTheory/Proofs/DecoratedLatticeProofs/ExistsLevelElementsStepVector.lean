import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitProductRescaleDisjointFinsets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockVecSum

theorem fockVec_eq_sum : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ t j, j + 1 < D.R.m → ∀ [Fintype (lvP W).H], ∃ κ : (lvP W).H → GA D (Yc D j), (∀ p, κ p ∈ levS (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W))) ∧ ∀ v, IsStepVecOf (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) ((pk W).ΛY j) ((pk W).ΛY (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) ((pk W).datYt t j (lvP W)) ((pk W).chi (j + 1)) ((pk W).Q t) ((pk W).xiR t) ((pk W).vac j) v → ∀ Q, pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) v Q = ∑ p, (levChi (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p))⁻¹ • ((pk W).ωY t j (κ p, 1)) ((pk W).ptY t j Q) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW t j hj _
  have hC := hW.bot.hyp.2.2.2.1
  have hL : (pk W).toLevCh.Is W.P.A3.A.μ0 := hC.lev
  have hj' : j < D.R.m := Nat.lt_of_succ_lt hj
  have hlift := GlobalTheory.ChainEquiv.lifts_chain (pk W).toLevCh W.P.A3.A.μ0 hL t j hj'
  choose κ hκ using fun p : (lvP W).H => hlift p.1
  refine ⟨κ, fun p => ⟨(hκ p).1, (hκ p).2.1, (hκ p).2.2 ▸ p.2⟩, fun v hv Q => ?_⟩
  obtain ⟨⟨a1, a2, a3⟩, b1, b2, b3⟩ := GlobalTheory.StepVecLaw.levRes_chrStep hL t ⟨j, hj'⟩
  obtain ⟨c, hc⟩ := hL.βY j hj'
  obtain ⟨c', hc'⟩ := hL.βY (j + 1) hj
  have hω := hC.chain.ωY t j hj
  have hvY := hC.chain.vY t j hj
  have hsum := GlobalTheory.StepVecSum.stepVec_eq_sum D (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) _ _ ((pk W).ωY t j) _ _
    ((pk W).ΛY j) ((pk W).ΛY (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) ((pk W).vac j) ((pk W).vY t j) v hω
    (D.sp.Y_sig _) (D.sp.Y_sig _) (GlobalTheory.Chain.VacVec.cart_isCartanInv ((pk W).MY j))
    (GlobalTheory.Chain.VacVec.cart_isCartanInv ((pk W).MY (j + 1)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY j hj'))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY (j + 1) hj)) hc.1 hc'.1 D.R.r D.R.t j (r_le_Y j)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj'.le]; rfl)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj.le]; rfl)
    (pk W).Pg ((pk W).Q t) (GlobalTheory.T.levelCharacters_unramified_off_levelPlaces D _ _ _ hL t).1 (pk W).chi ((pk W).xiR t) (lvP W) hvY hv
    (fun PP hP => ⟨a1 PP hP, b1 PP hP⟩) (fun PP hP => ⟨a2 PP hP, b2 PP hP⟩) a3 b3 κ hκ
  have hθ : IsInfFam (pk W).θ := hvY.1.2.inf
  have hf : IsThetaFunO (pk W).ψ (Yc D j) (Yc D (j + 1)) ((pk W).vY t j) := by
    have := hC.chain.ptY t j hj 1
    rwa [RealDat.ptY, GlobalTheory.FiniteFock.pureTensorO_one] at this
  rw [hsum, GlobalTheory.SpecFac.pureTensorO_sum hω.std hθ _ _ _ _ Finset.univ _ _ (fun p _ => hω.om_pres _ _ hf)]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  have hk := GlobalTheory.FiniteFock.compAt_mt_of_finite (pk W).θ
  refine ((GlobalTheory.OrientedHeis.om_pureTensorO D _ _ _ _ _ _ _ hω hθ _ _ _ _ _ _ _ _ (κ p) 1
    (fun τ => by rw [hk τ (hκ p).1, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hk τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hk τ (hκ p).1, Matrix.one_mul])
    (fun τ => by rw [hk τ (one_mem _), Matrix.one_mul]) _ hf Q).2).symm

end GlobalTheory.FockVecSum
