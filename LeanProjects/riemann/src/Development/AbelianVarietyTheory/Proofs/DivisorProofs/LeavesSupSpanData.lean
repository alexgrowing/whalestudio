import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeavesSupSpanLemmaSOfFormTieK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatAtAndSpanAtOfHypC
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional

set_option autoImplicit false

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem lat_span_of_hypC {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j) {large₂ : SizeData₂ D} {H : WeightAlgebra.KHyp}
    {C2 A2 CR Bx CT : ℝ} {S : WeightAlgebra.Scal (recB h.toLawsCore)} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    {nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ}
    (hyp : Formalism.MainNotions.Gaps.EtaleWeightGaps.HypC large₂ (recPJ h j hj) H C2 A2 CR Bx CT S ka wL wF Tn nP nW h0 nus) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h.toLawsCore) j ka ∧ ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ka ∧
      WeightAlgebra.H2 (recPJ h j hj) S ka wL wF := by
  obtain ⟨hA, -, hB, -, hH2, -⟩ := hyp
  obtain ⟨-, -, -, hK, -, po, -, -, PLam, -, -, -, -, hka⟩ := hB
  have sK := GlobalTheory.RunLat.spanAt_of_shortG _ _ _ _ hka
  exact ⟨GlobalTheory.latAt_record D _ h.toLawsCore (GlobalTheory.RunIn.gamAt_of_lawsCore' D _ h.toLawsCore) large₂ H.CA hA j ka _
    (recPJ h j hj) S wL wF hK sK hH2, sK, hH2⟩

theorem ownAt_pos (D : D7) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : 0 < ownAt D v := by
  unfold ownAt
  split_ifs
  · exact D.host.pde'_prime.pos
  · exact D.host.pde_prime.pos

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem leaves_sup_span_data : ∀ CK : ℝ, ∃ x₁ : ℝ, ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → CoreTies L EX J R → OwnPin r → PageNum Tp x₁ → RunsHold Tp hK EX CK r → R.IsGrp F → R.tup_mu_conj → R.tup_mu_off → R.tup_mu_ne → LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O ∧ LeafData O := by
  intro CK
  refine ⟨0, ?_⟩
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hrec _ _ _ hrun hgrp _ _ _
  obtain rfl : κ = fun i : Fin D.R.m => kaR Tp hK ((i : ℕ) + 1) := funext hrec.kap
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hrec.tied
  have hok := hrec.ok
  have h3 : LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O := by
    refine leaves_sup_span_lemmaS_of_formTieK GlobalTheory.chartIndependence_unconditional D L Pm Tp hK hinj EX _ _ _ _ _ c O
      fun v i => ?_
    letI : Algebra (r.used v).full.J.Q.c.F D.what₂.LL := inst
    obtain ⟨a1, a2, a3⟩ := lat_span_of_hypC _ _ (hrun v (hok.laws v).p hinj _ (inR_succ i)).1
    exact ⟨(r.used v).full, (hok.laws v).p, _, inR_succ i, ownAt D v, inst, z i, act i, fun g => r.lev i (mirIncl R g),
      (ht v i).1.toFormTieK, (ht v i).1.act_eq, hok.laws v, hok.xiRat v i, hok.cover v i, ownAt_pos D v, a1, a2, a3⟩
  refine ⟨h3.1, h3.2.1, h3.2.2, ?_⟩
  have hU : ∀ g, g ∈ F.P0 ↔ ∀ PP : R.Pg, R.eG g PP ∈ unip (kP PP.1) D.R.r := fun g => by
    rw [GlobalTheory.OntoChain.mem_base_iff hgrp.levels]
    refine Iff.trans ?_ ((mem_pi_unip_iff R (R.eG g)).symm.trans ⟨fun H PP => H PP (Set.mem_univ _), fun H PP _ => H PP⟩)
    refine exists_congr fun u => and_congr_right fun _ => ?_
    rw [← eG_mirIncl, R.eG.injective.eq_iff]
  have key : ∀ v (i : Fin D.R.m), GlobalTheory.TraceLattice.TiedAt A hinj EX O (mirIncl R) F.P0 F.ψ0⁻¹
      (fun _ _ _ _ _ _ _ _ _ => True) v i := fun v i =>
    ⟨(r.used v).full, inst, R, _, v₀, (hok.laws v).p, fw, ownAt D v, i, _, _, _, z i, act i, r.lev i, 1, y v i,
      (ht v i).1, hok.laws v, hok.xiRat v i, kaWt_n _ _ _ _, GlobalTheory.TraceLattice.kaR_lastPos Tp hK (inR_succ i),
      @GlobalTheory.TraceLattice.detOneOn_of_pins D G _ _ _ _ A (r.used v).full inst R i (hok.laws v) _ (hok.level v i) hok.half _ hU,
      trivial⟩
  exact GlobalTheory.TraceLattice.leafData_of_onTie_of_leafSpan h3.2.1 fun w _ => ⟨key w, key _⟩

end GlobalTheory.BigOn
