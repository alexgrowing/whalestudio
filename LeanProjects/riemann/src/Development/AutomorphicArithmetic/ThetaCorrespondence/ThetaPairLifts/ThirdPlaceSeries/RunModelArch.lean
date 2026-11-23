import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunWeightArch
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open GlobalTheory.RunJoin
namespace GlobalTheory.ShareOn
section Model
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end Model
section Run
end Run
section Point
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem p0_extreme_or_archOn_of_runModel : _root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x hx ι p r h => ∀ (i : Fin (Fm.D x ι).R.m) (C : Type) [Finite C]
    [MulAction p.P.Gp C] (M : TwoLevels (Fm.D x ι).host.E (Fm.D x ι).R.r p.P.Gp C) (ka : Wt M.Ψ (Fm.D x ι).R.r),
    RunModel p r h i M ka → (M.p0 = 0 ∨ M.p0 = (Fm.D x ι).R.r) ∨
      (0 < M.p0 ∧ M.p0 < (Fm.D x ι).R.r ∧ ArchOn M ka (Fm.parT x hx ι).TO) := by
  obtain ⟨x₀, hrun⟩ := GlobalTheory.FinalJoin.runHolds_of_parOK
  obtain ⟨CK, hCK⟩ := GlobalTheory.FinalJoin.RecordRun.exists_pageRun_record_sub_four
  obtain ⟨x₂, hpg⟩ := GlobalTheory.FinalJoin.pageOK_of_pageRun_beyond (fun _ _ => 0)
  refine Formalism.MainNotions.Closed.imp (GlobalTheory.T.runNumericalConditions_hold_along_family (max ((10 : ℝ) ^ 60) (max (x₀ 20 CK) (x₂ 20 CK)))) ?_
  intro eps Fm CH _ hx0
  obtain ⟨x0, hx0⟩ := hx0
  refine ⟨x0, fun x hx hle ι p _ hmore r hr hown i C _ _ M ka hRM => ?_⟩
  obtain ⟨⟨S, hCnW, hg, hC, hCZ, hxl⟩, -⟩ := hx0 x hx hle ι
  obtain ⟨-, hcore, -⟩ := hmore
  obtain ⟨v, e, hXc, hkaC, -⟩ := hRM
  have hl := hr.laws v
  have hj : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hinj := hcore.inj
  have hpar : ∀ j, InR (Fm.D x ι) j → ParOK (r.used v).full.toTop (Fm.ex x hx ι).errX (ownAt (Fm.D x ι) v) j :=
    GlobalTheory.FinalJoin2.liftIndexParameterConditions_of_coreAndShortLaws _ p.T _ _ _ hl.j hl.p hl.sh rfl hcore.canon (hcore.fieldAt v) hcore.halfEX
      (fun j hj n => ⟨hl.lvA j hj n, hown v j n hj⟩)
  have hO := (GlobalTheory.FinalJoin2.fieldSmall_iff_opo (Fm.D x ι) _ hl.p (Fm.L x ι)).1 hcore.small
  have hP := hCK (Fm.D x ι) (Fm.L x ι) _ (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def S hCnW hg
    ((le_max_left _ _).trans hxl) hC hCZ _ _ _ (recPJ hl.p ((i : ℕ) + 1) hj) hj hO
  have hHC := (hrun (Fm.D x ι) _ hl.p hinj _ _ hpar ((i : ℕ) + 1) hj (Fm.L x ι) _ _ _ _ _ _ _ _ _ _ _ hP
    (((le_max_left _ _).trans (le_max_right _ _)).trans hxl)).2.1
  have hOK := (hpg (Fm.D x ι) _ _ ((i : ℕ) + 1) (recPJ hl.p ((i : ℕ) + 1) hj) (Fm.L x ι) _ _ _ _ _ _ _ _ _ _ _ hj hP
    (((le_max_right _ _).trans (le_max_right _ _)).trans hxl)).1
  have hwd := fun k => GlobalTheory.Shares.WtDic.weights_dictionary (Fm.D x ι) (r.used v).full.toTop hl.p ((i : ℕ) + 1) hj k
  haveI : Nonempty C := ⟨e.symm ((r.used v).full.toTop.dict ((i : ℕ) + 1) (r.used v).full.toTop.σ₀ 1).1⟩
  obtain ⟨c0⟩ := ‹Nonempty C›
  have hp0M : M.p0 = ((Fm.D x ι).R.sigW ((i : ℕ) + 1)).2 :=
    (M.comp_basePoint c0).symm.trans ((congrArg Data.p0 (hXc c0)).trans (hwd (e c0)).2.2.2.2.2.1)
  have hq : ((Fm.D x ι).R.sigW ((i : ℕ) + 1)).2 = (Fm.D x ι).R.m - ((i : ℕ) + 1) := rfl
  have hr : (Fm.D x ι).R.r = (Fm.D x ι).R.k + (Fm.D x ι).R.m - 1 := rfl
  have hk := (Fm.D x ι).R.m_add_three_le_k
  by_cases hjm : (i : ℕ) + 1 < (Fm.D x ι).R.m
  swap
  · left; left; rw [hp0M, hq]; omega
  right
  refine ⟨by rw [hp0M, hq]; omega, by rw [hp0M, hq, hr]; omega, ?_⟩
  have hκ : p.κ i = kaR (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def ((i : ℕ) + 1) :=
    GlobalTheory.BigOn.eq_kaR _ _ i (p.κ i) (fun τ => ((fw2 p).kap i τ).1) (fun τ => ((fw2 p).kap i τ).2.1)
      ((fw2 p).kap i (GlobalTheory.RunDepth.plOf _ (false, Classical.arbitrary _))).2.2
  have hΨ : M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c0)).Ψ :=
    (M.comp_Ψ c0).symm.trans (congrArg Data.Ψ (hXc c0))
  have hcard : M.Ψ.card = (Fm.D x ι).R.f := by rw [hΨ]; exact (hwd (e c0)).2.2.2.2.2.2.1
  have hr1 : 1 ≤ (Fm.D x ι).R.r := by rw [hr]; omega
  have hdim : WeightFamilies.dimY (Fm.D x ι) ((i : ℕ) + 1) = M.dimY := by
    unfold TwoLevels.dimY
    rw [hcard]
    have h2 := GlobalTheory.ArchInputs.two_mul_dimY _ hj
    have h3 : ((2 * WeightFamilies.dimY (Fm.D x ι) ((i : ℕ) + 1) : ℕ) : ℝ) =
        (((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1)) : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hr1]
      linarith
    have h4 : 2 * WeightFamilies.dimY (Fm.D x ι) ((i : ℕ) + 1) = (Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1)) :=
      by exact_mod_cast h3
    obtain ⟨t, ht⟩ := Nat.even_mul_pred_self (Fm.D x ι).R.r
    rw [ht] at h4 ⊢
    rw [show (t + t) / 2 = t by omega]
    rw [mul_add] at h4
    linarith
  refine archOn_of_comps M ka (fun k => ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k) e hXc
    (fun k => laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k)
    (fun k => laR (r.used v).full.toTop ((i : ℕ) + 1) (lR (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def ((i : ℕ) + 1)) k)
    (fun k => laR (r.used v).full.toTop ((i : ℕ) + 1) (fR (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def ((i : ℕ) + 1)) k)
    (Fm.parT x hx ι).TO _ hdim hkaC (fun k => ?_) (fun k k' τ h h' a => ?_) (fun k k' τ h h' a => ?_)
    (fun k => run_weight_arch _ _ hl.p _ hj _ _ _ _ _ _ _ _ _ _ _ _ _ hOK.hyp hjm k)
    (fun k => archOne_of_run _ _ hl.p hinj _ _ _ hj _ _ _ _ _ _ _ _ _ _ _ _ _ (hpar _ hj) hOK hHC hjm k)
  · show laR _ _ (p.κ i) k = _
    rw [hκ, ← (GlobalTheory.SharesDefinite.weight_and_degree hOK.hyp).1]
    exact (hwd k).2.2.1 _ _ _
  · simp only [GlobalTheory.Shares.laR, Formalism.L2.Pj.laU, (hwd k).2.2.2.2.2.1, (hwd k').2.2.2.2.2.1]
  · simp only [GlobalTheory.Shares.laR, Formalism.L2.Pj.laU, (hwd k).2.2.2.2.2.1, (hwd k').2.2.2.2.2.1]
end Point
end GlobalTheory.ShareOn
end
end
