import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelCharStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLift.Level

variable {D : D7}

theorem isLift_one_V {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (t : T0) :
    Lev.IsLevelLift (Vc D i) (L.βV i) (L.datVt i t) 1 1 := by
  have h : (1 : GA D (Vc D i)) ∈ Lev.levG (Vc D i) (L.βV i) (L.datVt i t) := one_mem _
  exact ⟨h.1, h.2.1, Subgroup.mem_bot.1 h.2.2⟩

theorem levChi_flag_one {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    Lev.levChi V β (Lev.flagL L) 1 = 1 := by
  unfold Lev.levChi
  rw [(Lev.finE V).map_one]
  exact congrArg Units.val (Formalism.L2.DIV.levChar D.sp.cm V.gram β (Lev.flagL L)).map_one

theorem om_level_vP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_ωP → R.thP_vP → (∀ i t, IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t)) → ∀ i t, ∀ k ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv), R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hω hv _ i t k hk
  have h := GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hL (hv i t).1.2.inf hω hv i t 1 1 k (isLift_one_V R.toLevCh i t)
    ⟨hk.1, hk.2.1, Subgroup.mem_bot.1 hk.2.2⟩
  rw [h, levChi_flag_one, inv_one, one_smul]

end GlobalTheory.DefLift.Level
