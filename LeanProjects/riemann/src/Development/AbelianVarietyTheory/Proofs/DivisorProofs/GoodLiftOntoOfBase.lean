import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodFormsCoordinateMapMemOfLiftsMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelCharStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TraceIncl

namespace GlobalTheory.BaseTwistIncl

section Rank

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem ws_le_base (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (h5 : (R.toCx F).H5 F.cr false) (i : Fin D.R.m) (t : T0)
    (N : Submodule ℂ (R.HW i (sg0 D A)).H) (hN : ∀ x, R.thG i t (jVx R i t (OnTies.srcForm A i t F.P0 F.ψ0⁻¹ x)) ∈ N) :
    R.WS F false i (sg0 D A) ≤ N := by
  intro w h1
  obtain ⟨c, hc⟩ := exists_w0C_eq R F i h1
  have h0 : ∀ y, (R.toCx F).θ' i t ((R.toCx F).jL i t (F.cr.toL (R.toCx F).zs false i t y)) ∈
      Tw.sub (twAt D.what₂.embLL A.v0) N := by
    intro y
    obtain ⟨x, hx⟩ := exists_srcForm_eq F hX i t ((R.toCx F).zs.Zl i t) y
    have k5 : ∀ u u' : A.fam.amb.FL i t, u = u' → R.thG i t (jVx R i t u) ∈ N → R.thG i t (jVx R i t u') ∈ N :=
      fun u u' h hu => h ▸ hu
    have k4 := k5 _ _ hx (hN x)
    have k3 := out_lift_toL R F i t y
    exact (congrArg (fun u : (R.HW i (sg0 D A)).H => u ∈ N) k3).mpr k4
  have h2 := goodFormsCoordinateMap_mem_of_lifts_mem (R.toCx F) F.cr false h5 i t _ h0 c
  exact (congrArg (· ∈ N) hc).mp h2

theorem goodLiftOnto_of_base (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (hW : R.models_HW) (hG : R.thP_thG) (hU : R.LUnif)
    (h5 : (R.toCx F).H5 F.cr false) (i : Fin D.R.m) (t : T0) (ph : ℂ) (hph : ph ≠ 0) :
    GoodLiftOnto R i t F.P0 F.ψ0⁻¹ ph := by
  intro θ hθ z hz
  refine mem_of_mem_span_image ((R.FW i).j (sg0 D A)) (hU i _).1 _ ?_
  have h1 : (R.FW i).j (sg0 D A) z ∈
      Submodule.span ℂ (Set.range fun x => R.thG i t (jVx R i t (OnTies.srcForm A i t F.P0 F.ψ0⁻¹ x))) := by
    refine ws_le_base R F hX h5 i t _ (fun x => Submodule.subset_span (Set.mem_range_self x)) ?_
    rw [GlobalTheory.LevelForms.ws_eq_span]
    exact Submodule.subset_span ⟨z, hz, rfl⟩
  refine Submodule.span_le.2 ?_ h1
  rintro _ ⟨x, rfl⟩
  refine (Submodule.smul_mem_iff _ hph).1 ?_
  exact Submodule.subset_span ⟨_, ⟨x, rfl⟩, j_eOp_of_adForm R hW hG hU i t ph _ _ (hθ x)⟩

end Rank

attribute [local instance] GlobalTheory.BigOn.runAlg'

theorem leafTW2_of_isRec : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ s : ℕ, A.fam.Ok s → R.Char F → R.LUnif → BaseLinks R F → TwistedRational R F (fun _ => 1) → LeafTW2 O := by
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hrec s hOk hC hU hB hrat
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hrec.tied
  have hinc : F.P0 ≤ (mirIncl R).range := fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff hC.grp.levels g).1 hg
    exact ⟨u, e⟩
  have main : ∀ v, (∀ j, ClassSumRational R j (R.mu v) F.P0 F.ψ0⁻¹ 1) →
      ∀ j, IsLatIn (O.Zg j) (O.X₃ v j) ∧ IsLatIn (O.Zg j) (O.Im v j) ∧
        Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.X₃ v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Im v j) := by
    intro v h3 j
    have := lattices_of_tie (T := (r.used v).full) (inst := inst) (R := R)
      (ht v j).1 (ht v j).2 hinc (chi_eq_one_of_mem_base R F hC.grp j)
      ⟨hC.lev, hC.grp.red_L, hC.fam.tie, hC.models, hC.thP, hU, ⟨_, (fw.hv₀ j _).1⟩, (hOk.lifts _ _).act,
        GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hC.lev hC.models.inf hC.thP.ωP hC.thP.vP j (R.mu v)⟩
      (hOk.lifts _ _).good hOk.irr (h3 j)
      (goodLiftOnto_of_base R F hOk.irr hC.models.HW hC.thP.thG hU hB.1 _ _ _ one_ne_zero)
    exact ⟨this.1, this.2.1, Formalism.L2.DIV.localization_mono _ this.2.2⟩
  intro w hw
  exact ⟨main w (hrat w hw), main _ (by rw [hC.tup.mu_conj w]; exact hrat w hw)⟩

end GlobalTheory.BaseTwistIncl
