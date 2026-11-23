import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelCharStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.LevelFix

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem isLiftFiniteGroup_one_of_mem_coeffSpaceLevel (R : RealDat D A Ks) (i : Fin D.R.m) (k : GA D (Wc D i)) (hk : k ∈ levW R i) :
    IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 k := by
  refine ⟨hk.1, hk.2.1, ?_⟩
  have h2 := hk.2.2
  have e : (R.datWp i R.triv).P.H = ⊥ := rfl
  rw [e] at h2
  exact Subgroup.mem_bot.1 h2

theorem realDatum_identity_lifts_identity (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

theorem levChi_flag_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) 1 = 1 := by
  have := (levChar D.sp.cm (Vc D i).gram (R.βV i) (flagL (R.datVt i t))).map_one
  unfold levChi
  rw [map_one]
  exact congrArg Units.val this

theorem levW_fix_vP (R : RealDat D A Ks) (F : Face D A) (h : Laws R F) (i : Fin D.R.m) (t : T)
    (k : GA D (Wc D i)) (hk : k ∈ levW R i) : R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
  have e := GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R h.lev h.models.inf h.thP.ωP h.thP.vP i t 1 1 k (realDatum_identity_lifts_identity R i t)
    (isLiftFiniteGroup_one_of_mem_coeffSpaceLevel R i k hk)
  rw [e, levChi_flag_one R i t, inv_one, one_smul]

theorem levFix : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    Laws R F → R.FullP → ∀ i t, LevFix R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F h _ i t k hk P
  have hv : R.ωP i t (1, k) (R.vP i t) = (1 : ℂ) • R.vP i t := by
    rw [one_smul]; exact levW_fix_vP R F h i t k hk
  have := GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) h.models.inf
    (h.thP.ωP i t) _ _ _ _ _ (h.thP.pt_theta i t) 1 (Subgroup.one_mem _) k hk.1 1 hv P
  exact this.trans (one_smul ℂ _)

end GlobalTheory.RawLift.LevelFix

end
