import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusOneDatumModelLatticeAlgebraicData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeColumnsModelParameterSeries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MvPowerSeriesThreeEqZeroOfSubstLines
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.SigmaAdd

open PowerSeries

def gap {R τ : Type} [CommRing R] (s T : PowerSeries R) (x y : MvPowerSeries τ R) : MvPowerSeries τ R :=
  subst (x + y) s * subst (x - y) s - (subst x s * subst x s * subst y T - subst y s * subst y s * subst x T)

theorem mv_subst_subst {R σ τ : Type} [CommRing R] {b : σ → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b)
    {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries R) :
    MvPowerSeries.subst b (subst a f : MvPowerSeries σ R) = subst (MvPowerSeries.subst b a) f := by
  have has : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => ha
  rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply has hb]
  rfl

theorem subst_gap {R τ : Type} [CommRing R] (s T : PowerSeries R) {b : Fin 3 → MvPowerSeries τ R}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (gap s T (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) R) =
      gap s T (b 0) (b 1) := by
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R) = 0 := by simp
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) = 0 := by simp
  have hp : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) = 0 := by simp
  have hm : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) = 0 := by simp
  simp only [gap, MvPowerSeries.subst_sub hb, MvPowerSeries.subst_mul hb, mv_subst_subst hb h0,
    mv_subst_subst hb h1, mv_subst_subst hb hp, mv_subst_subst hb hm, MvPowerSeries.subst_add hb,
    MvPowerSeries.subst_X hb]

theorem map_gap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (s T : PowerSeries R) :
    MvPowerSeries.map φ (gap s T (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) R) =
      gap (PowerSeries.map φ s) (PowerSeries.map φ T) (MvPowerSeries.X 0) (MvPowerSeries.X 1) := by
  have e : ∀ (a : MvPowerSeries (Fin 3) R), MvPowerSeries.constantCoeff a = 0 → ∀ f : PowerSeries R,
      MvPowerSeries.map φ (subst a f) = subst (MvPowerSeries.map φ a) (PowerSeries.map φ f) :=
    fun a ha f => PowerSeries.map_subst (HasSubst.of_constantCoeff_zero ha) f
  simp only [gap, map_sub, map_mul]
  rw [e _ (by simp), e _ (by simp), e _ (by simp), e _ (by simp), e _ (by simp), e _ (by simp)]
  simp only [map_add, map_sub, MvPowerSeries.map_X]

theorem add_entire {Λ : AddSubgroup ℂ} (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) (z w : ℂ) :
    sgStar Λ (z + w) * sgStar Λ (z - w) =
      sgStar Λ z * sgStar Λ z * sqTh Λ v w - sgStar Λ w * sgStar Λ w * sqTh Λ v z := by
  have h1 := (h.differentiable_sqTh v).continuous
  have h3 := h.differentiable.continuous
  refine congrFun (Continuous.ext_on h.dense_compl
    (f := fun z => sgStar Λ (z + w) * sgStar Λ (z - w))
    (g := fun z => sgStar Λ z * sgStar Λ z * sqTh Λ v w - sgStar Λ w * sgStar Λ w * sqTh Λ v z)
    (by fun_prop) (by fun_prop) fun z hz => ?_) z
  beta_reduce
  have h0 := (h.sg_eq_zero z).not.2 hz
  have e : sgStar Λ (z + w) * sgStar Λ (z - w) = sgStar Λ z ^ 2 * sqTh Λ z w := by
    rw [sqTh]; field_simp
  rw [e, h.sqTh_sub hz hv w, h.sqTh_eq hv hz]
  ring

theorem tay_mul {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) :
    PowerSeries.mk (coef1 fun z => F z * G z) = PowerSeries.mk (coef1 F) * PowerSeries.mk (coef1 G) := by
  ext n
  simp only [coeff_mul, coeff_mk, GlobalTheory.SerTransport.taylorCoeff_mul_entire hF hG]

theorem tay_add {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) :
    PowerSeries.mk (coef1 fun z => F z + G z) = PowerSeries.mk (coef1 F) + PowerSeries.mk (coef1 G) := by
  ext n
  simp only [map_add, coeff_mk, GlobalTheory.SerTransport.taylorCoeff_add_entire hF hG]

theorem tay_scale {F : ℂ → ℂ} (hF : Differentiable ℂ F) (c : ℂ) :
    (subst (C c * X : PowerSeries ℂ) (PowerSeries.mk (coef1 F)) : PowerSeries ℂ) =
      PowerSeries.mk (coef1 fun z => F (c * z)) := by
  rw [← smul_eq_C_mul, ← rescale_eq_subst]
  ext n
  simp only [coeff_rescale, coeff_mk, GlobalTheory.SerTransport.taylorCoeff_scale_entire hF]

theorem gap_taylor {Λ : AddSubgroup ℂ} (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) :
    (gap (PowerSeries.mk (coef1 (sgStar Λ))) (PowerSeries.mk (coef1 (sqTh Λ v)))
      (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) ℂ) = 0 := by
  refine GlobalTheory.mvPowerSeries_three_eq_zero_of_subst_lines ℂ _ fun t => ?_
  have hb : MvPowerSeries.HasSubst (fun i => (C (t i) * X : PowerSeries ℂ)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
      rw [map_mul]; exact mul_eq_zero_of_right _ (PowerSeries.constantCoeff_X (R := ℂ))
  have hs := h.differentiable
  have hT := h.differentiable_sqTh v
  refine (subst_gap _ _ hb).trans ?_
  have key : (subst (C (t 0 + t 1) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) : PowerSeries ℂ) *
      subst (C (t 0 - t 1) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) +
      subst (C (t 1) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) *
        subst (C (t 1) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) *
        subst (C (t 0) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sqTh Λ v))) =
      subst (C (t 0) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) *
        subst (C (t 0) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) *
        subst (C (t 1) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sqTh Λ v))) := by
    simp only [tay_scale hs, tay_scale hT]
    rw [← tay_mul (by fun_prop) (by fun_prop), ← tay_mul (by fun_prop) (by fun_prop),
      ← tay_mul (by fun_prop) (by fun_prop), ← tay_mul (by fun_prop) (by fun_prop),
      ← tay_mul (by fun_prop) (by fun_prop), ← tay_add (by fun_prop) (by fun_prop)]
    congr 2
    funext z
    rw [add_mul, sub_mul, add_entire h hv]
    ring
  rw [map_add, map_sub, add_mul, sub_mul] at key
  unfold gap
  linear_combination key

variable {p : ℕ} [Fact p.Prime]

theorem sigmaAdditionFormula_padicTransfer_of_algebraicTaylor (lam : Qbar →+* ℂ_[p]) {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G)
    (h : (gap (PowerSeries.mk (coef1 F)) (PowerSeries.mk (coef1 G))
      (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) ℂ) = 0) :
    (gap (GL3Theta.ser1 lam F) (GL3Theta.ser1 lam G)
      (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
  have e : ∀ {H : ℂ → ℂ}, AlgEnt H → ∃ S : PowerSeries Qbar,
      PowerSeries.mk (coef1 H) = PowerSeries.map (algebraMap Qbar ℂ) S := fun {H} hH =>
    ⟨PowerSeries.mk fun n => ⟨coef1 H n, hH.2 n⟩, by
      ext n; rw [coeff_map, coeff_mk, coeff_mk]; rfl⟩
  obtain ⟨s, hs⟩ := e hF
  obtain ⟨T, hT⟩ := e hG
  rw [hs, hT, ← map_gap] at h
  have h' : (gap s T (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) Qbar) = 0 := by
    ext d
    have := congrArg (MvPowerSeries.coeff d) h
    rw [MvPowerSeries.coeff_map, map_zero] at this
    simpa using this
  rw [Param.theta_series_map_coefficients lam _ _ hs, Param.theta_series_map_coefficients lam _ _ hT, ← map_gap, h', map_zero]

theorem const_subst {τ : Type} {a : MvPowerSeries τ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    {f : PowerSeries ℂ_[p]} (hf : constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (subst a f : MvPowerSeries τ ℂ_[p]) = 0 := by
  obtain ⟨f', rfl⟩ := X_dvd_iff.2 hf
  have hs := HasSubst.of_constantCoeff_zero ha
  rw [subst_mul hs, subst_X hs, map_mul, ha, zero_mul]

theorem subst_inv {τ : Type} {a : MvPowerSeries τ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    {f : PowerSeries ℂ_[p]} (hf : constantCoeff f ≠ 0) :
    (subst a f⁻¹ : MvPowerSeries τ ℂ_[p]) = (subst a f : MvPowerSeries τ ℂ_[p])⁻¹ := by
  have hs := HasSubst.of_constantCoeff_zero ha
  have e : (subst a f⁻¹ : MvPowerSeries τ ℂ_[p]) * subst a f = 1 := by
    rw [← subst_mul hs, PowerSeries.inv_mul_cancel _ hf, ← coe_substAlgHom hs, map_one]
  refine (MvPowerSeries.eq_inv_iff_mul_eq_one fun h0 => ?_).2 e
  have := congrArg MvPowerSeries.constantCoeff e
  rw [map_mul, h0, mul_zero, map_one] at this
  exact zero_ne_one this

theorem subst_atU (g : GL3Theta.G1 p) {τ : Type} {a : MvPowerSeries τ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (F : ℂ → ℂ) : (subst a (g.atU F) : MvPowerSeries τ ℂ_[p]) =
      subst (MvPowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.lg a) (GL3Theta.ser1 g.lam F) := by
  have hs := HasSubst.of_constantCoeff_zero ha
  rw [GlobalTheory.SerTransport.atU_eq, subst_comp_subst_apply
    (HasSubst.of_constantCoeff_zero' (GlobalTheory.SerTransport.const_Cl g _)) hs, subst_mul hs, subst_C]
  rfl

theorem lg_pt (g : GL3Theta.G1 p) (hg : g.Ok) {τ : Type} {x : MvPowerSeries τ ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) : g.lg (g.pt x) = x := by
  have hs := HasSubst.of_constantCoeff_zero hx
  rw [GL3Theta.G1.lg, GL3Theta.G1.pt, ← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hg.2.2.1) hs,
    hg.2.2.2, subst_X hs]

theorem sigma_add_param : ∀ D : D7, Formalism.MainNotions.Ext.CutA.PAdicSigmaAdditionFormula D := by
  intro D p _ cc δ g hA
  obtain ⟨hq, hL, h2, h3, hσ, v, hv, hw⟩ := GlobalTheory.FrobStick.AtData.atData D p cc δ g hA
  have hok : g.Ok := hA.2.2.2.2
  obtain ⟨aT, eT⟩ := Param.sqTh_atU p g hq hL h2 h3 hσ v hv hw
  have eS := GlobalTheory.FrobStick.sgStar_atU g hL hσ
  have hgap := sigmaAdditionFormula_padicTransfer_of_algebraicTaylor g.lam hσ aT (gap_taylor hL hv)
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε
  have hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (GL3Theta.Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hl : ∀ i : Fin 2, MvPowerSeries.constantCoeff (g.lg (GL3Theta.Xv i) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    fun i => const_subst (hX i) (GlobalTheory.SerTransport.const_l g)
  have hb : MvPowerSeries.HasSubst (![MvPowerSeries.C ε * g.lg (GL3Theta.Xv 0), MvPowerSeries.C ε * g.lg (GL3Theta.Xv 1), 0] :
      Fin 3 → MvPowerSeries (Fin 2) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
      fin_cases i <;> simp [hl]
  have k := subst_gap (GL3Theta.ser1 g.lam (sgStar g.abelian₂)) (GL3Theta.ser1 g.lam (sqTh g.abelian₂ v)) hb
  rw [hgap, ← MvPowerSeries.coe_substAlgHom hb, map_zero] at k
  have hp0 : MvPowerSeries.constantCoeff
      (g.lg (GL3Theta.Xv 0) + g.lg (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by simp [hl]
  have hm0 : MvPowerSeries.constantCoeff
      (g.lg (GL3Theta.Xv 0) - g.lg (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by simp [hl]
  have hp : MvPowerSeries.constantCoeff (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    const_subst hp0 hok.2.2.1
  have hm : MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    const_subst hm0 hok.2.2.1
  have kp := subst_atU g hp (sgStar g.abelian₂)
  have km := subst_atU g hm (sgStar g.abelian₂)
  rw [show g.lg (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = _ from lg_pt g hok hp0] at kp
  rw [show g.lg (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = _ from lg_pt g hok hm0] at km
  simp only [gap, Matrix.cons_val_zero, Matrix.cons_val_one, ← mul_add, ← mul_sub] at k
  rw [← kp, ← km, ← subst_atU g (hX 0), ← subst_atU g (hX 0), ← subst_atU g (hX 1), ← subst_atU g (hX 1),
    eS, eT] at k
  have sS : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff a = 0 →
      (subst a (C ε * X * ePhi1 g.lam g.abelian₂ g.C g.wq) : MvPowerSeries (Fin 2) ℂ_[p]) =
        MvPowerSeries.C ε * a * subst a (ePhi1 g.lam g.abelian₂ g.C g.wq) := fun a ha => by
    have hs := HasSubst.of_constantCoeff_zero ha
    rw [subst_mul hs, subst_mul hs, subst_X hs, subst_C]
  have hwq : constantCoeff g.wq ≠ 0 := by
    have e := congrArg constantCoeff (show g.wq = _ from hq)
    simp only [map_add, map_mul, map_pow, map_one, constantCoeff_X] at e
    rw [e]
    simp
  have sT : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff a = 0 →
      (subst a (ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * lineSer g.wq⁻¹ (xAt g v)) : MvPowerSeries (Fin 2) ℂ_[p]) =
        subst a (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 2 *
          ((subst a g.wq : MvPowerSeries (Fin 2) ℂ_[p])⁻¹ - MvPowerSeries.C (xAt g v) * a ^ 2) := fun a ha => by
    have hs := HasSubst.of_constantCoeff_zero ha
    rw [lineSer, subst_mul hs, subst_pow hs, subst_sub hs, subst_mul hs, subst_pow hs, subst_X hs, subst_C,
      subst_inv ha hwq]
  rw [sS _ hp, sS _ hm, sS _ (hX 0), sS _ (hX 1), sT _ (hX 0), sT _ (hX 1)] at k
  have hne : (MvPowerSeries.C ε : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 ≠ 0 := by
    refine pow_ne_zero 2 fun h => Units.ne_zero g.C.u⁻¹ ?_
    have e := congrArg MvPowerSeries.constantCoeff h
    rwa [MvPowerSeries.constantCoeff_C, map_zero] at e
  apply mul_left_cancel₀ hne
  linear_combination -k

end GlobalTheory.SigmaAdd
