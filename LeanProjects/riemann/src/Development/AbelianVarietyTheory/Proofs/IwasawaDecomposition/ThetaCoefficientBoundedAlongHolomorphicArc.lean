import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyAtIffExistsKeyAtVia
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumThetaGeneratorChartRatio
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaCharOffNeZeroDifferentiableQuasiPeriodic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNeZeroIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaCharHalfDifferentiableNeZeroFamilies
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsPChartOfFramedPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaConstantUniformisedChartFibreEqFamilyConstaStatement
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ArcNormal

theorem exists_chart_theta_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ (κ : ℂ) (r : PowerSeries ℂ) (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)), κ ≠ 0 ∧ PowerSeries.constantCoeff r ≠ 0 ∧ IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ ∧ IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ ∧ ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∃ rw : ℂ, SumsAt r w rw ∧ ∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u Ha.i (Ha.Pw w)) (fun z => (Fu.ex Ha.i (Ha.Pw w) z).left) (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) fr → ∀ (z : Fin g → ℂ) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (M.θ j) = valAt' x _ (w₁.s (fun _ => j, k)).val * ((κ * rw) * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) * fr j₀ z) := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M hgood hty hPI hχ hrng hM
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hL2 := GlobalTheory.abelianSchemeLaws_all.2
  obtain ⟨hA, hB⟩ := GlobalTheory.theta_generates_along_arc hL.globalFns hL.secBaseChange Y a χ W
  have hw0 : Ha.T < ((Ha.T + 1 : ℝ) * Complex.I : ℂ).im := by simp
  have hne : ∃ j, th.f j ≠ 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨hs, hp⟩ := Θ.pos _ hw0
    have h7 := (GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic g Θ.S (Θ.τ ((Ha.T + 1 : ℝ) * Complex.I)) Θ.c₁ Θ.c₂ hs hp Θ.half₁ Θ.half₂ Θ.c₁_S).1
    apply h7
    funext v
    set w := ((Ha.T + 1 : ℝ) * Complex.I : ℂ) with hwdef
    have hz : Θ.h.mulVec (∑ k, v k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1))) = v := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, (Θ.per w _).1]
      exact (pi_eq_sum_univ' v).symm
    rw [← hz]
    generalize (∑ k, v k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1))) = z
    obtain ⟨fr, -, n, -, -, hv⟩ := Θ.onB w hw0
    obtain ⟨j, hj⟩ := exists_chart a.D₀.P.isLB ((show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) (IsLocalRing.closedPoint ℂ))
    have hU : ⊤ ≤ (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) ⁻¹ᵁ a.D₀.P.L.U j := fun q _ =>
      (Subsingleton.elim (α := PrimeSpectrum ℂ) (IsLocalRing.closedPoint ℂ) q) ▸ hj
    have e := hv j z hU
    have e0 : valAt' (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) (a.D₀.P.L.U j) (th.f j) = 0 := by
      rw [hc j]
      exact (dif_pos hU).trans ((congrArg _ (map_zero _)).trans (map_zero _))
    rw [e0] at e
    have := (mul_eq_zero.1 e.symm).resolve_right (n j z hU)
    exact (mul_eq_zero.1 this).resolve_left Θ.κ_ne
  have hth : GlobalTheory.ArcQ.ThNZ th := ((GlobalTheory.ThetaOverField.nonzero_generates hL hL2 ℂ a.D₀ th).1).1 hne
  obtain ⟨⟨t, ht, -⟩, hnz⟩ := hB th
  obtain ⟨σ0, fam, hfam0, hexp, -, -, -, -, ⟨w₂, hw₂⟩, hrest⟩ := hA t (hnz t ht hth _)
  have hpull : GlobalTheory.ThetaUnit.IsPullTerm W.P.D.toPre W.φ W.w th (fam 0) := hfam0 ▸ ht
  obtain ⟨-, hr⟩ := (hrest w₂ hw₂.1).2 hPI
  obtain ⟨r, hr⟩ := hr M.U M.θ hM ⟨M.θ_mem, M.gen⟩
  obtain ⟨w₀, h₀⟩ := GlobalTheory.Reg.ChartInhab.exists_rigIso Y.m0.toSABMap
  obtain ⟨w₁, h₁⟩ := GlobalTheory.Reg.ChartInhab.exists_rigIso Y.m
  obtain ⟨fr₀, hfr₀⟩ := Θ.frame _ hw0
  obtain ⟨κ, hκ, -, -, hmain⟩ := Ha.theta th σ0 fam Θ.bas Θ.S Θ.h Θ.τ Θ.c₁ Θ.c₂ w₂ w₁ w₀ hne hexp hpull Θ.sympl Θ.ker Θ.per Θ.half₁ Θ.half₂ hw₂ h₁ h₀ ⟨_, fr₀, hw0, hfr₀⟩
  obtain ⟨T', hT'⟩ := hmain M.U M.θ r.val hM M.θ_mem hr
  refine ⟨κ, r.val, w₀, w₁, hκ, ?_, h₀, h₁, T', hT'⟩
  exact ((PowerSeries.isUnit_iff_constantCoeff).1 r.isUnit).ne_zero

theorem exists_bounds_of_sumsAt : ∀ (κ : ℂ), κ ≠ 0 → ∀ r : PowerSeries ℂ, PowerSeries.constantCoeff r ≠ 0 → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ rw : ℂ, SumsAt r w rw → C⁻¹ ≤ ‖κ * rw‖ ∧ ‖κ * rw‖ ≤ C := by
  intro κ hκ r hr0
  by_cases hex : ∃ w₀ rw₀, SumsAt r w₀ rw₀
  swap
  · exact ⟨0, 1, one_pos, fun w _ rw h => (hex ⟨w, rw, h⟩).elim⟩
  obtain ⟨w₀, rw₀, h₀⟩ := hex
  have hq₀ : 0 < ‖eTwoPi w₀‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  obtain ⟨B, hB⟩ : ∃ B, ∀ n, ‖PowerSeries.coeff n r * eTwoPi w₀ ^ n‖ ≤ B := by
    obtain ⟨B, hB⟩ := h₀.summable.tendsto_atTop_zero.norm.bddAbove_range
    exact ⟨B, fun n => hB ⟨n, rfl⟩⟩
  have ha₀ : 0 < ‖PowerSeries.constantCoeff r‖ := norm_pos_iff.2 hr0
  have hκ' : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  set A := ‖PowerSeries.constantCoeff r‖ with hA
  set B' := max B 1 with hB'
  have hB'1 : 1 ≤ B' := le_max_right _ _
  set t : ℝ := min (1 / 2) (A / (4 * B')) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (div_pos ha₀ (by linarith))
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have htB : t ≤ A / (4 * B') := min_le_right _ _
  have htB' : 4 * B' * t ≤ A := by
    have := mul_le_mul_of_nonneg_left htB (by linarith : (0:ℝ) ≤ 4 * B')
    rwa [mul_div_cancel₀ _ (by linarith : (4 * B' : ℝ) ≠ 0)] at this
  refine ⟨-Real.log (t * ‖eTwoPi w₀‖) / (2 * Real.pi), max (3 / 2 * (‖κ‖ * A)) (2 / (‖κ‖ * A)),
    lt_max_of_lt_left (by positivity), fun w hw rw hrw => ?_⟩
  have hqn : ‖eTwoPi w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
    simp [eTwoPi, Complex.norm_exp]
  have hq : ‖eTwoPi w‖ ≤ t * ‖eTwoPi w₀‖ := by
    rw [hqn]
    have hpos : 0 < t * ‖eTwoPi w₀‖ := mul_pos ht0 hq₀
    rw [← Real.exp_log hpos]
    apply Real.exp_le_exp.2
    have := (div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)).1 hw
    linarith
  have hf := (hasSum_nat_add_iff' 1).2 hrw
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hf
  have hg : HasSum (fun n : ℕ => B' * t * t ^ n) (B' * t * (1 - t)⁻¹) :=
    (hasSum_geometric_of_lt_one ht0.le (by linarith)).mul_left (B' * t)
  have hle : ‖rw - PowerSeries.constantCoeff r‖ ≤ B' * t * (1 - t)⁻¹ := by
    refine hf.norm_le_of_bounded hg fun n => ?_
    have h1 : ‖PowerSeries.coeff (n + 1) r‖ * ‖eTwoPi w₀‖ ^ (n + 1) ≤ B' := by
      have := hB (n + 1)
      rw [norm_mul, norm_pow] at this
      exact this.trans (le_max_left _ _)
    rw [norm_mul, norm_pow]
    calc ‖PowerSeries.coeff (n + 1) r‖ * ‖eTwoPi w‖ ^ (n + 1)
        ≤ ‖PowerSeries.coeff (n + 1) r‖ * (t * ‖eTwoPi w₀‖) ^ (n + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq _) (norm_nonneg _)
      _ = (‖PowerSeries.coeff (n + 1) r‖ * ‖eTwoPi w₀‖ ^ (n + 1)) * t ^ (n + 1) := by ring
      _ ≤ B' * t ^ (n + 1) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = B' * t * t ^ n := by ring
  have h2 : B' * t * (1 - t)⁻¹ ≤ A / 2 := by
    have h1t : 0 < 1 - t := by linarith
    rw [← div_eq_mul_inv, div_le_iff₀ h1t]
    nlinarith
  have hlo : A / 2 ≤ ‖rw‖ := by
    have := norm_sub_norm_le (PowerSeries.constantCoeff r) rw
    rw [norm_sub_rev] at this
    linarith
  have hhi : ‖rw‖ ≤ 3 / 2 * A := by
    have := norm_sub_norm_le rw (PowerSeries.constantCoeff r)
    linarith
  rw [norm_mul]
  constructor
  · have hx : 0 < ‖κ‖ * A := mul_pos hκ' ha₀
    calc (max (3 / 2 * (‖κ‖ * A)) (2 / (‖κ‖ * A)))⁻¹ ≤ (2 / (‖κ‖ * A))⁻¹ :=
          inv_anti₀ (by positivity) (le_max_right _ _)
      _ = ‖κ‖ * (A / 2) := by field_simp
      _ ≤ ‖κ‖ * ‖rw‖ := mul_le_mul_of_nonneg_left hlo hκ'.le
  · calc ‖κ‖ * ‖rw‖ ≤ ‖κ‖ * (3 / 2 * A) := mul_le_mul_of_nonneg_left hhi hκ'.le
      _ = 3 / 2 * (‖κ‖ * A) := by ring
      _ ≤ _ := le_max_left _ _

theorem theta_const_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig → GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) → C⁻¹ ≤ ‖c₀‖ ∧ ‖c₀‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M hgood hty hPI hχ hrng hM
  obtain ⟨κ, r, w₀, w₁, hκ, hr0, h₀, h₁, T', hT'⟩ := exists_chart_theta_unit E H Dw l Xo c σ V Y a χ W g ty Fu Ha th Θ M hgood hty hPI hχ hrng hM
  obtain ⟨T₃, C, hC, hb⟩ := exists_bounds_of_sumsAt κ hκ r hr0
  refine ⟨max T' (max Ha.T T₃), C, hC, fun w hw yF e₁ e₂ hz x φ hx u c₀ hrig hfib hfn => ?_⟩
  simp only [max_lt_iff] at hw
  obtain ⟨rw, hrw, hval⟩ := hT' w hw.1
  obtain rfl := GlobalTheory.T.thetaConstant_uniformisedChartFibre_eq_familyConstant E H Dw l Xo c σ V Y a χ W g ty Fu Ha th Θ M hgood hty hPI hχ hrng hM w hw.2.1 w₀ w₁ h₀ h₁ (κ * rw) hval yF e₁ e₂ hz x φ hx u c₀ hrig hfib hfn
  exact hb w hw.2.2 rw hrw

end GlobalTheory.ArcNormal
