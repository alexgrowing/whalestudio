import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FreeHalfOfDeformationSpace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsFreeHalfLiftOfNeat
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Keeps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSplitDeformationLift

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT
noncomputable section
namespace GlobalTheory.DefHalf
set_option maxHeartbeats 1000000 in
theorem halfH_acts_freely_on_internal_sum_decomposition : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ k : Fin 2,
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) X)
      (A : X → Submodule ℂ (GlobalTheory.DefRead.VAt p i)),
      (∀ (h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) (y : X), ∀ v ∈ A y,
        GlobalTheory.DefRead.repAt p i (h : G0g (Fm.D x ι).nd) v ∈ A (h • y) := by
  intro hP hG
  have h1 := _root_.GlobalTheory.T.freePt_lev2_halfH_at_last_index hP hG
  have h2 := _root_.GlobalTheory.T.exists_isInternal_free_permuted_thirdPlace hP hG
  unfold _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine Closed.imp (h1.and h2) ?_
  rintro eps Fm CH - ⟨⟨C1, -, x1, ha1⟩, ⟨C2, -, x2, ha2⟩⟩
  refine ⟨0, le_rfl, max x1 x2, fun x hx hle ι p hp i hi k => ?_⟩
  have a1 := ha1 x hx (le_trans (le_max_left _ _) hle) ι p hp i hi k
  have a2 := ha2 x hx (le_trans (le_max_right _ _) hle) ι p hp i hi hp (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k)
    (((p.R.eG.trans p.cG).symm.toMonoidHom).comp (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k).subtype) a1
  obtain ⟨X, hX, hdX, hact, A, hfr, hint, hperm⟩ := a2
  letI := ((p.R.toRealDat.FW i)).towKs
  obtain ⟨n, b, hbW, hbK, hbsK, hbL, hbsL⟩ := p.fw.ks i
  have hK := (p.rhoGeo i).1 (fun g f hf => _root_.GlobalTheory.DefHalf.keeps_alt p i hp.1 g f hf)
  have he : ∀ g f, (((p.fw.e i) (_root_.GlobalTheory.DefHalf.groupActionOnCoefficients p i hp.1 g f) : (p.R.FW i).WK) : Fin (p.R.nW i) → (Fm.D x ι).what₂.LL) =
      (p.R.FW i).ρ g ((p.fw.e i) f) := by
    intro g f
    obtain ⟨hf, h⟩ := hK g f
    rw [← h]
    rfl
  obtain ⟨A', hint', hperm'⟩ := GlobalTheory.T.transport_permuted_directSum_complexification p.T.Q.c.F (Fm.D x ι).what₂.LL (Fin (p.R.nW i) → (Fm.D x ι).what₂.LL) (CF p i)
    (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) p.P.Gp X (Fm.D x ι).what₂.embLL (p.R.FW i).WK n b hbW hbK hbsK hbL hbsL
    (p.fw.e i) (p.R.FW i).ρ (p.R.FW i).chi (_root_.GlobalTheory.DefHalf.groupActionOnCoefficients p i hp.1) he
    (((p.R.eG.trans p.cG).symm.toMonoidHom).comp (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k).subtype) A hint hperm
  exact ⟨X, hX, hdX, hact, A', hfr, hint', fun h y v hv => hperm' h y v hv⟩
end GlobalTheory.DefHalf
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfH_free_action_and_isInternal_repAt_mem : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ k : Fin 2,
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) X)
      (A : X → Submodule ℂ (GlobalTheory.DefRead.VAt p i)),
      (∀ (h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) (y : X), ∀ v ∈ A y,
        GlobalTheory.DefRead.repAt p i (h : G0g (Fm.D x ι).nd) v ∈ A (h • y) := by
  first | exact @_root_.GlobalTheory.DefHalf.halfH_acts_freely_on_internal_sum_decomposition | exact _root_.GlobalTheory.DefHalf.halfH_acts_freely_on_internal_sum_decomposition | (intros; apply _root_.GlobalTheory.DefHalf.halfH_acts_freely_on_internal_sum_decomposition <;> assumption)
end
end
