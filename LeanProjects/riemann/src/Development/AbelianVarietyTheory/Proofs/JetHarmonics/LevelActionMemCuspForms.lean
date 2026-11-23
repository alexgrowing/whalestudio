import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPointsStatement
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteDimensionalOfLeHolSub
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEqConstMulOfForallExistsNormEqStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRationalIsometryOfTraceIsometryStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotAntiIsometryOfTriangularRelatedPeriodsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FramesDifferByIsometryAndTriangularOfPeriodsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryTriangularPeriodsOfFramePointMoveStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemCuspFormsOfMultipleRationalIsometryMoveStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMoveStatement

namespace GlobalTheory.LevelCusp

section Free

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Formalism.L2.PjFree.Unf Xo c σ r}

theorem exists_match (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ r)
    (hxi : ∀ k k' (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ‖τ (U.X k').ξ0‖)
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} {k k' : U.Comp} {x : (U.X k).dom} {x' : (U.X k').dom}
    {y' : FrPt Xo c (CAt σ)} {t : Ix Dw → (CAt σ)ˣ} (hm : FrMove ρ ν (U.un k x) y') (hb : FrBor t (U.un k' x') y')
    (hx : IsUnitFr (U.X k) x.1) (hx' : IsUnitFr (U.X k') x'.1) :
    ∃ (a : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k') a), ∃ b ∈ Bor (U.X k').Ψ r,
      x'.1 = rmul (lact a (castFr h.psi x.1)) b ∧ (∀ τ i, ‖b τ i i‖ = 1) ∧ ∀ j, cabs (t j : CAt σ) = 1 := by
  obtain ⟨gam, A, htr, hA0, hA, hAt⟩ := GlobalTheory.T.exists_isometry_triangular_periods_of_framePointMove E H Dw l Xo c σ r U hσ hU ρ ν k k' x x' y' t hm hb
  have hgen := GlobalTheory.T.abs_generatorRatio_eq_one_of_unitFrame_move E H Dw l Xo c σ r U hσ hU ρ ν k k' x x' y' t hm hb hx hx'
  obtain ⟨a, ε, hε, hξ, hav, hlat, hiso⟩ := GlobalTheory.T.exists_rational_isometry_of_trace_isometry E r (U.X k) (U.X k') (hxi k k') gam htr
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hrr, hty, -⟩ := hU
  have hΨ : (U.X k).Ψ = (U.X k').Ψ := Finset.ext fun τ => ((hty k).2 τ).trans ((hty k').2 τ).symm
  have hp : (U.X k).p0 = (U.X k').p0 := (hty k).1.trans (hty k').1.symm
  let e := Equiv.ofBijective _ hbij
  have he : ∀ τ, Formalism.L2.PjFree.relab c σ (e.symm τ) = τ := e.apply_symm_apply
  have m1 : ∀ τ ∈ (U.X k).Ψ, Dw.mult (e.symm τ) = r - (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_pos ((hrt _).1 (by rw [he]; exact ((hty k).2 τ).1 hτ)), (hty k).1]
    omega
  have m2 : ∀ τ ∉ (U.X k).Ψ, Dw.mult (e.symm τ) = (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg (fun h => hτ (((hty k).2 τ).2 (by rw [← he τ]; exact (hrt _).2 h))), (hty k).1]
  have hrel : ∀ τ, ∀ i < Dw.mult (e.symm τ), ∀ v ∈ (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k') x'.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
        ∑ j ∈ Finset.range (Dw.mult (e.symm τ)), A (e.symm τ) i j * Formalism.L2.PjFree.perFr (U.X k) x.1 v τ j :=
    fun τ i hi v hv => by
      have := hA (e.symm τ) i hi ⟨v, hv⟩
      rwa [he, ← hav] at this
  rcases hε with rfl | rfl
  · have h : IsMatch (U.X k) (U.X k') a :=
      ⟨hΨ, hp, by rw [hξ, one_mul], fun u v => by rw [hiso, one_mul], hlat⟩
    obtain ⟨b, hb, hxb, hu⟩ := GlobalTheory.T.frames_differ_by_isometry_and_triangular_of_periods E r _ _ a h (fun τ => Dw.mult (e.symm τ)) m1 m2 x.1 x.2 x'.1 x'.2
      (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel
    obtain ⟨h1, h2⟩ := hu hx hx'
    refine ⟨a, h, b, hb, hxb, h1, fun j => ?_⟩
    rcases j with _ | ⟨τ, i⟩
    · exact hgen
    · have := h2 (e τ) i (by rw [e.symm_apply_apply]; exact i.2)
      rw [e.symm_apply_apply, hAt] at this
      exact this
  · exact (GlobalTheory.T.not_antiIsometry_of_triangular_related_periods E r _ _ hΨ hp hr a hiso (fun τ => Dw.mult (e.symm τ)) m1 m2 x.1 x.2 x'.1 x'.2
      (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel).elim

theorem laU_match {k k' : U.Comp} {a : GL (Fin r) E} (h : IsMatch (U.X k) (U.X k') a)
    (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : (U.X k').Ψ) (i : Fin r) :
    Formalism.L2.PjFree.laU U w n k' τ i = Formalism.L2.PjFree.laU U w n k ⟨τ.1, h.mem τ⟩ i := by
  unfold Formalism.L2.PjFree.laU
  rw [h.p0]

theorem rdU_mem_SS (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ r)
    (hxi : ∀ k k' (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ‖τ (U.X k').ξ0‖) {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom w n)
    {f g : Rul Xo c} (hf : f ∈ sec Xo c w n) (hg : g ∈ sec Xo c w n)
    (hfc : ∀ k, Formalism.L2.PjFree.rdU U f k ∈ (U.X k).SS (Formalism.L2.PjFree.laU U w n k))
    (hmv : ∀ y : FrPt Xo c (CAt σ), ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (y' : FrPt Xo c (CAt σ)),
      FrMove ρ ν y y' ∧ evR Xo c g y = evR Xo c f y') (k : U.Comp) :
    Formalism.L2.PjFree.rdU U g k ∈ (U.X k).SS (Formalism.L2.PjFree.laU U w n k) := by
  have hsec := hU.2.2.2.2.1 w n hD g hg k
  obtain ⟨hun1, hun2⟩ := GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r U hσ hU
  obtain ⟨⟨k', a, h⟩, c₀, hc⟩ := GlobalTheory.T.exists_eq_const_mul_of_forall_exists_norm_eq' (Frame (U.X k).Ψ r)
    (Σ k' : U.Comp, {a : GL (Fin r) E // IsMatch (U.X k) (U.X k') a}) (U.X k).dom (FourierCoefficientDomain.isOpen_dom _)
    (GlobalTheory.frames_isConnected E r (U.X k)).isPreconnected (GlobalTheory.frames_isConnected E r (U.X k)).nonempty
    (Formalism.L2.PjFree.rdU U g k) (fun i x => Formalism.L2.PjFree.rdU U f i.1 (lact i.2.1 (castFr i.2.2.psi x))) hsec.1
    (fun i => (hfc i.1).1.1.1.comp ((GlobalTheory.Dict.Extend.differentiable_lact i.2.1).comp
      (GlobalTheory.Dict.Pull.cast_diff i.2.2.psi)).differentiableOn fun x hx => i.2.2.mem_dom hx)
    (fun x hx => by
      obtain ⟨x₀, hx₀, ⟨b₀, hb₀, e₀⟩, -⟩ := hun1 k ⟨x, hx⟩
      obtain ⟨ρ, ν, y', hm, hv⟩ := hmv (U.un k x₀)
      obtain ⟨k', x', t, hx', hb⟩ := hun2 y'
      obtain ⟨a, h, b, hbB, hxb, hb1, ht⟩ := exists_match hσ hU hr hxi hm hb hx₀ hx'
      refine ⟨⟨k', a, h⟩, ?_⟩
      have hQ := (hfc k').1.1
      have v1 : Formalism.L2.PjFree.rdU U g k x₀.1 = Formalism.L2.PjFree.toC (evR Xo c g (U.un k x₀)) := dif_pos x₀.2
      have v2 : Formalism.L2.PjFree.rdU U f k' x'.1 = Formalism.L2.PjFree.toC (evR Xo c f (U.un k' x')) := dif_pos x'.2
      have v3 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 (CAt σ)
        (inferInstanceAs (IsReduced ℂ)) w n f hf t _ y' hb
      have v4 : ‖Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ)‖ = 1 := by
        have : Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ) =
          ∏ j, Formalism.L2.PjFree.toC (t j : CAt σ) ^ ex Dw w n j := rfl
        rw [this, norm_prod]
        exact Finset.prod_eq_one fun j _ => by
          rw [norm_pow, show ‖Formalism.L2.PjFree.toC (t j : CAt σ)‖ = 1 from ht j, one_pow]
      have v5 : ‖Formalism.L2.PjFree.rdU U g k x₀.1‖ = ‖Formalism.L2.PjFree.rdU U f k' x'.1‖ := by
        rw [v1, v2, hv, v3]
        exact (norm_mul (Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ)) _).trans (by rw [v4, one_mul]; rfl)
      have v6 : ‖bchar (Formalism.L2.PjFree.laU U w n k') b‖ = 1 := by
        unfold bchar
        simp only [norm_prod, norm_zpow, hb1, one_zpow, Finset.prod_const_one]
      rw [hxb, hQ.2.1 _ (h.mem_dom x₀.2) b hbB, norm_mul, v6, one_mul, e₀, hsec.2.1 x hx b₀ hb₀,
        GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul,
        hQ.2.1 _ (h.mem_dom hx) _ (GlobalTheory.Dict.Pull.cast_bor h.psi hb₀),
        GlobalTheory.Dict.Pull.cast_bchar h.psi (laU_match h w n), norm_mul, norm_mul] at v5
      exact mul_left_cancel₀ (norm_ne_zero_iff.2 (AR.Up.OntoE.bchar_ne _ _ hb₀)) v5)
  exact GlobalTheory.T.mem_cuspForms_of_multiple_rational_isometry_move E r _ _ a h _ _ (laU_match h w n) _ _ c₀ hsec (hfc k') hc

end Free

end GlobalTheory.LevelCusp

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

theorem GlobalTheory.LevelCusp.actLev_mem_cuspA : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), ∀ f ∈ T.cuspA j (wtA w) w.n, actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ T.cuspA j (wtA w) w.n := by
  intro D T h j hj w γ f hf
  have hp := h.pins
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.T.actLev_full_level_group_framedPoints D T.Q j hpq hp.2.1.2
  obtain ⟨hs, hc⟩ := (mem_cusp _ _ _ _ _ _).1 hf
  have hg : actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n :=
    actL_mem _ _ _ _ hL.total hL.nat hL.bor _ γ hs
  refine (mem_cusp _ _ _ _ _ _).2 ⟨hg, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩
  have hU := h.unf j hj σ hσ
  refine GlobalTheory.LevelCusp.rdU_mem_SS (U := Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU (hU.1 ▸ hpq)
    (fun k k' τ => (h.xiAbs j hj σ hσ k τ).trans (h.xiAbs j hj σ hσ k' τ).symm) (dom_wtA w) hs hg
    (fun k => GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ (hc σ hσ) k) (fun y => ?_) k
  obtain ⟨ρ, ν, -, -, hm⟩ := mvPt_spec hL.total γ y
  exact ⟨ρ, ν, _, hm, evalAt_actL hL (h.evalWD j hj) frMap_trans_id γ hs.1 y⟩
