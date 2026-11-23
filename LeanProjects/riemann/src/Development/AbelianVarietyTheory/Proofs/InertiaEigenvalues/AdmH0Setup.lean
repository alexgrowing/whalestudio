import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Formalism.SharpRestriction.LevelLetterCocycles.JumpAndLengthOfAdmitted
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfCrystallineLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointCondH0allCanon
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostCompletionLeMaxUnramifiedPadic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentKillsInvariantsNoJumpZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeWachModuleExistsProofStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlacesAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StatementJAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAway
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousTwistedDualRhoO
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.PowerSmulVanishing

theorem pow_smul_eq_zero_of_le {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (p : O) {a b : ℕ}
    (h : a ≤ b) {x : M} (hx : p ^ a • x = 0) : p ^ b • x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, mul_comm, ← smul_smul, hx, smul_zero]

set_option maxHeartbeats 1600000 in

theorem main : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.H0ColumnLengthBound i (X.ρ i) π (X.dc i) (X.c0 i) := by
  intro hP D L P nch HW F Cm X C₂ hS i hTw hg hRA hSp π hπ
  have hJ : AdmissibleParameterJ.JumpConditions L := GlobalTheory.JumpStatement.holds_all D L (hS.facts.admJ L hS.par)
  obtain ⟨M0, h0, hl2, hJC⟩ := GlobalTheory.HubX.jointCondH0all_canon hP.font D L HW (rowC C₂) X hS.canon hJ
    hS.facts.Conclusion1.1 (GlobalTheory.FontaineAdm.fontaineProperties_all_places D) i hTw hg hRA hSp π hπ
  have hlq : D.nd.l i ≠ D.host.q := fun h => hRA.2.1 (Or.inl h)
  have hld : D.nd.l i ≠ D.host.d := fun h => hRA.2.1 (Or.inr h)
  intro _ u hu w hw hconj C hC L2 hstd
  obtain ⟨-, hall⟩ := hJC u hu w hw hconj
  have hur : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) := GlobalTheory.HubLoc.kw_le_Kur_all D i (fun h => hRA.1 (Or.inl h)) hlq hld w hw
  have hg1 : Good (D.nbr i w hw).Kw 1 C.LL := hC.good_one hl2 (le_trans (le_inf le_rfl hur) le_sup_left)
  have hT2c : Continuous fun g => T2O D.nd i (X.ρ i) π g :=
    GlobalTheory.HTW.RecS.Model.continuous_twistedDual_rhoO i (X.ρ i) π (hS.canon.fam.cont i π)
  have hc : ∀ v, Continuous fun g => matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i (X.ρ i) π)) g v :=
    fun v => (GlobalTheory.CrysChiOne.locC_cont' C _ hT2c).matrix_mulVec continuous_const
  obtain ⟨hcr, hwin, hnj, hc0⟩ := hall C hg1 hc L2
  have hW := GlobalTheory.T.crystallineLatticeWachModuleExists_proof D HW F Cm (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hg1 (GlobalTheory.HubX.tTwoLocalLattice D i (X.ρ i) π C hc L2) M0 h0 hcr hwin
  have hkill := GlobalTheory.T.torsion_exponent_kills_invariants_of_good hP.bk hP.tate hP.euler D HW F Cm (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hg1 M0 h0
    (GlobalTheory.HubX.tTwoLocalLattice D i (X.ρ i) π C hc L2) hW hnj
  unfold EmbeddingTypes.lenInvD
  haveI : IsDiscreteValuationRing ↥(OL C.LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr C.LL
  haveI : IsFractionRing ↥(OL C.LL) ↥C.LL.1 := Formalism.BasicNotions.Examples₂.LB.OL_frac C.LL
  refine EmbeddingTypes.len_le_of_kill (Br.PD D.loc D.nbr i w hw) L2.T hstd _ (X.c0 i u) ?_
  intro x hx
  exact pow_smul_eq_zero_of_le _ hc0 (hkill x fun g => hx g)

end GlobalTheory.NLink.PowerSmulVanishing
