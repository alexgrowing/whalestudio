import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsSplitDeformationLift
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Keeps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftWeightNumerator
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.DefSplit
section Alg
open scoped TensorProduct
variable {K L B W : Type} [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B] [AddCommGroup W] [Module K W]
end Alg
section Geo
open CategoryTheory Limits AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient (fnAt basePt)
open GlobalTheory.LevelCoverCompare (fnRule fnRule_mem fnRule_injective fnAt_comp)
variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
variable {G : Type} [Group G] {lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}
end Geo
section Main
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
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem exists_free_action_permuting_summands_thirdPlace : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ (hp : _root_.GlobalTheory.CovTop.RowsTAlt p) (Hg : Type) [Group Hg] [Finite Hg] (φ : Hg →* p.P.Gp),
    GlobalTheory.DefPt.FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun h => (p.O i).lev2 (φ h)) →
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction Hg X) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (GlobalTheory.DefHalf.sigC p) (GlobalTheory.DefHalf.CF p i))),
      (∀ (h : Hg) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : Hg) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (GlobalTheory.DefHalf.sigC p) (_root_.GlobalTheory.DefHalf.groupActionOnCoefficients p i hp.1 (φ h)) v ∈ A (h • y) := by
  intro _ _
  have hw : _root_.GlobalTheory.CovTop.LiftWeightNumerator := _root_.GlobalTheory.CovTop.WtShape.wtN_z
  unfold _root_.GlobalTheory.CovTop.LiftWeightNumerator _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine Closed.imp hw ?_
  rintro eps Fm CH - ⟨C, hC, x0, ha⟩
  refine ⟨C, hC, x0, fun x hx hle ι p hp i hi hp' Hg _ _ φ hF => ?_⟩
  have hW := ha x hx hle ι p hp i
  have hj : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨Nat.succ_pos _, hi.le⟩
  have hq : (p.T.Q.Dw ((i : ℕ) + 1)).q = 0 := by
    have : (dat p i).q = (Fm.D x ι).R.m - ((i : ℕ) + 1) := by rw [hW.sig.2.1]; rfl
    simpa [dat, hi] using this
  have hU := p.fw.laws.unf _ hj
  have h : ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.O i).lev2 := (p.pins i).2.act.1
  have hL : ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun g : Hg => (p.O i).lev2 (φ g)) :=
    ⟨fun g => h.total (φ g), fun g => h.func (φ g), fun S _ _ y => by
        have := h.one S y
        rw [← map_one φ] at this
        exact this,
      fun g g' S _ _ y y' y'' a b => by
        have := h.mul (φ g) (φ g') S y y' y'' a b
        rw [← map_mul φ] at this
        exact this,
      fun g => h.nat (φ g), fun g => h.bor (φ g)⟩
  refine split_rules hq hL hF (GlobalTheory.DefHalf.CF p i) (fun b f hf => ?_) (fun g => _root_.GlobalTheory.DefHalf.groupActionOnCoefficients p i hp'.1 (φ g))
    (fun g f => rfl) _
  refine GlobalTheory.DefPt.ReadsPt.mem_cusp_of_sec hq hU hW.dom ?_
  have := sec_mul _ _ _ _ _ _ (GlobalTheory.LevelCoverCompare.fnRule_mem b) (cusp_le_sec _ _ _ _ _ hf)
  rwa [zero_add, zero_add] at this
end Main
end GlobalTheory.DefSplit
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
open Formalism.IndefR.FWT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isInternal_free_permuted_thirdPlace : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ (hp : _root_.GlobalTheory.CovTop.RowsTAlt p) (Hg : Type) [Group Hg] [Finite Hg] (φ : Hg →* p.P.Gp),
    GlobalTheory.DefPt.FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun h => (p.O i).lev2 (φ h)) →
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction Hg X) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (GlobalTheory.DefHalf.sigC p) (GlobalTheory.DefHalf.CF p i))),
      (∀ (h : Hg) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : Hg) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (GlobalTheory.DefHalf.sigC p) (_root_.GlobalTheory.DefHalf.groupActionOnCoefficients p i hp.1 (φ h)) v ∈ A (h • y) := by
  first | exact @_root_.GlobalTheory.DefSplit.exists_free_action_permuting_summands_thirdPlace | exact _root_.GlobalTheory.DefSplit.exists_free_action_permuting_summands_thirdPlace | (intros; apply _root_.GlobalTheory.DefSplit.exists_free_action_permuting_summands_thirdPlace <;> assumption)
end
end
