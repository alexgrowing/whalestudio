import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel
import Development.AutomorphicArithmetic.LocalEmbeddings.JetsGrid
import Development.AutomorphicArithmetic.LocalEmbeddings.JetsTest
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSummandEmbeddingHom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedKernelExpansionSumLevelInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CastMulUnitaryAdelicGroupOfEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section
open GlobalTheory.DefStep GlobalTheory.JetsOne GlobalTheory.ExpansionInvariance

private theorem last_ok {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T} (hL : L.Is μ0) (Λ : Module.Dual ℂ (VV ℂ (wt G (.top D.R.m))))
    (Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))) :
    ∃ (c : ℂ) (s : GA D (G.V (.grid D.R.m D.R.m)) →* GA D (G.V (.top D.R.m))), (∀ h, stabilizerEmbedding G.sp.topDec h = s h) ∧
      LastOK (realAct W.θ S.N.fr (.top D.R.m)) Λ (realAct W.θ S.N.fr (.grid D.R.m D.R.m)) Λ' s (finEmb G.sp.topDec)
        (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid D.R.m D.R.m))
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hdef := GlobalTheory.TopIntegral.isDefinite_last G
  haveI : CompactSpace (GinfC (G.V (.grid D.R.m D.R.m))) := isCompact_iff_compactSpace.1 (Eqv.isCompact_GinfC hdef.1 hdef.2)
  obtain ⟨κ₀, k1, k2⟩ := exists_haar _ hdef
  obtain ⟨c, hc⟩ := GlobalTheory.TopIntegral.real_average W.θ_is S.N Λ Λ' κ₀
  obtain ⟨s, h1, h2, h3⟩ := GlobalTheory.TopIntegral.exists_orthogonal_summand_embedding_hom G.sp.topDec
  refine ⟨c, s, h2, hdef, posDef_grid hL le_rfl, fun g hg => realAct_fin _ _ _ hg, fun g hg => realAct_fin _ _ _ hg, h1, h3,
    fun z => (h2 _).symm.trans (GlobalTheory.RealType.Emb_fin _ z), fun k hk => h2 k ▸ GlobalTheory.RealType.Emb_mem_inf _ hk,
    fun u u' => ?_, fun κ a1 a2 u u' => ?_⟩
  · simp only [← h2]
    exact (GlobalTheory.TopIntegral.continuous_integrand W.θ_is S.N Λ Λ' u u').comp continuous_subtype_val
  · obtain rfl : κ = κ₀ := Measure.isHaarMeasure_eq_of_isProbabilityMeasure κ κ₀
    simp only [← h2]
    exact hc u u'

private theorem pair_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (c : ℂ) (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0)))
    (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))) (X : ∀ j, FinPt G (.top j))
    (Y : ∀ i, FinPt G (.grid i D.R.m)) :
    c * pairPts S τ X Y (Ψ (X 0)) (F (Y 0)) = τ.sum fun d a => a *
      GlobalTheory.JetsOne.pairP (V := fun j => G.V (.top j)) (V' := fun j => G.V (.grid j D.R.m)) (Mo := fun j => VV ℂ (wt G (.top j)))
        (Mo' := fun j => VV ℂ (wt G (.grid j D.R.m))) (colComp S d) (fun x => rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ (Ψ x))
        (rowComp S d) (fun x => rhoVr (tauE D) (wt G (.grid 0 D.R.m)) (S.N.fr (.grid 0 D.R.m))⁻¹
          (funOf (listedWt G (.grid 0 D.R.m)) (F x))) D.R.m
        (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) X Y := by
  rw [pairPts, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  refine (mul_left_comm c (τ d) _).trans (congrArg (τ d * ·) ?_)
  exact (congrArg₂ (fun a b => (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) a b)
    (ptV_eq_chainTo (V := fun j => G.V (.top j)) (Mo := fun j => VV ℂ (wt G (.top j))) (colComp S d)
      (fun x => rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ (Ψ x)) X D.R.m)
    (ptV_eq_chainTo (V := fun j => G.V (.grid j D.R.m)) (Mo := fun j => VV ℂ (wt G (.grid j D.R.m))) (rowComp S d)
      (fun x => rhoVr (tauE D) (wt G (.grid 0 D.R.m)) (S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt G (.grid 0 D.R.m)) (F x)))
      Y D.R.m)).symm

end

theorem _root_.GlobalTheory.T.term_volume_class_sum : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → Big fun ch => ∀ P : PolCol ch.G × PolRow ch.G, ∃ κ : ℂ, ∀ t a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M τ, IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ch.S.IsExpansion t (ch.Phi a) β τ → ∀ y, defTot t ch.S.toGridChoice M (Finsupp.single P 1) τ (colFn ch a) (formTop ch t y) = κ * ch.S.classSum (ch.Phi a) β τ (psiC (ch.Psi a)) (ch.S.formC t y) := by
  intro hP hS
  obtain ⟨C0, H⟩ := Big.and hS (GlobalTheory.FirstRowLaw.first_level_invariance hP hS)
  refine ⟨C0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc P => ?_⟩
  obtain ⟨hOK, h0⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch hi hsc
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨Λ0, hΛ0⟩ := GlobalTheory.JetsOne.col_real ch
  obtain ⟨Λ0', hΛ0'⟩ := GlobalTheory.JetsOne.form_real ch s.core.models.cX
  obtain ⟨Λ, rfl, hΛ⟩ := GlobalTheory.JetsOne.col_chain ch.S.toGridChoice hL P Λ0
  obtain ⟨Λ', rfl, hΛ'⟩ := GlobalTheory.JetsOne.row_chain ch.S.toGridChoice hL P Λ0'
  obtain ⟨c, σ, hσ, hlast⟩ := last_ok ch.S.toGridChoice hL (Λ D.R.m) (Λ' D.R.m)
  refine ⟨c, fun t a β hβ M τ hM hτ y => ?_⟩
  have hv := (hOK t a).vec β τ hτ
  obtain ⟨v1, v2⟩ := TermVolDef.isMeasDef_of_isTermVol ch.S.toGridChoice hL t _ β M hM
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.T.normalisedKernelExpansionSum_levelInvariant ch.S.toGridChoice hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hi.guard t)
    (Set.mem_univ t) hβ hτ hv (psiC (ch.Psi a)) (ch.S.formC t y)
  have hK0 : ∀ h : 0 < D.R.m, ch.S.levTop t (ch.Phi a) β 0 h = ch.G.Kplus := fun _ => rfl
  have key := GlobalTheory.JetsOne.glue (V := fun j => ch.G.V (.top j)) (V' := fun j => ch.G.V (.grid j D.R.m)) τ
    (fun d hd => hΛ t (Set.mem_univ t) d (hv d hd).1) (hΛ0 a) (GlobalTheory.JetsOne.col_left ch a)
    (fun d hd => GlobalTheory.JetsOne.col_near _ P d (hv d hd).1 (GlobalTheory.JetsOne.col_fix ch a (v1 0 hm).2.1))
    (fun d hd => hΛ' t (Set.mem_univ t) d (hv d hd).2) (hΛ0' t y) (GlobalTheory.JetsOne.form_aut s ch t y).1
    (fun d hd => GlobalTheory.JetsOne.row_near _ P d (hv d hd).2 (GlobalTheory.JetsOne.form_aut s ch t y).2) hlast
    (fun n hn => posDef_top ch.G hn.le) (fun n hn => posDef_grid hL hn)
    (fun j => M.ν (.top j)) (fun j => M.fd (.top j)) (ch.S.levTop t (ch.Phi a) β) (fun n hn => (v1 n hn).2)
    (fun j => M.ν (.grid j D.R.m)) (fun j => M.fd (.grid j D.R.m)) (ch.S.levRow t) (fun n hn => (v2 n hn).2)
    (fun X Y => c * GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ X Y (psiC (ch.Psi a) (X 0)) (ch.S.formC t y (Y 0)))
    (pair_eq ch.S.toGridChoice τ c _ _)
    (fun X Y j hj k hk => by
      rcases j with _ | j
      · have := i2 (GlobalTheory.JetsOne.psiC_right ch a) X Y k hk
        beta_reduce
        rw [Function.update_self, this]
      · exact congrArg _ (i1 X Y _ j.succ_pos hj k hk))
    (fun X Y j hj k hk => by
      rcases j with _ | j
      · have := h0 t a β hβ τ hτ y (psiC (ch.Psi a) (X 0)) X Y k hk
        beta_reduce
        rw [Function.update_self, this]
      · exact congrArg _ (i3 X Y _ j.succ_pos hj k hk))
    (fun X Y k h1 hk => congrArg _ (i4 X Y k h1 hk))
  rw [defTot, Finsupp.sum_single_index (by simp)]
  simp only [one_mul, GlobalTheory.JetsOne.defPer_eq, hσ]
  refine key.trans ?_
  rw [GridChoice.classSum, mul_finsum]
  exact finsum_congr fun c' => mul_left_comm _ _ _
