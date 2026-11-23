import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThCoefA

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LThCoef

variable {D : D7}

abbrev Sp (W : HSp D) (n : ℕ) : Type := {x : Matrix (Fin W.rank) (Fin n) D.host.E // x.rank = W.rank}

instance countable_sp (W : HSp D) (n : ℕ) : Countable (Sp W n) := by
  have := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  have : Countable (Matrix (Fin W.rank) (Fin n) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin n → D.host.E))
  infer_instance

theorem ip_inv (W : HSp D) {n : ℕ} (h : GA D W) (y : Matrix (Fin W.rank) (Fin n) D.host.E) :
    ip W (mm (mt W h⁻¹) (rat y)) (mm (mt W h⁻¹) (rat y)) = rat (gramQ W y) := by
  have hu := GlobalTheory.RatAut.mt_unitary W h⁻¹
  have hr := GlobalTheory.CompanionTheory.ThetaCoefND.rat_gramQ W y
  show ((Formalism.L2.Theta.mt W h⁻¹ * y.map (Formalism.L2.Theta.incA D)).map (Formalism.L2.Theta.cA D)).transpose *
      ((Formalism.BasicNotions.HSpace.gram W).map (Formalism.L2.Theta.incA D) *
        (Formalism.L2.Theta.mt W h⁻¹ * y.map (Formalism.L2.Theta.incA D))) =
    (gramQ W y).map (Formalism.L2.Theta.incA D)
  rw [hr]
  show _ = ((y.map (Formalism.L2.Theta.incA D)).map (Formalism.L2.Theta.cA D)).transpose *
      ((Formalism.BasicNotions.HSpace.gram W).map (Formalism.L2.Theta.incA D) * y.map (Formalism.L2.Theta.incA D))
  rw [Matrix.map_mul, Matrix.transpose_mul]
  calc _ = ((y.map (Formalism.L2.Theta.incA D)).map (Formalism.L2.Theta.cA D)).transpose *
        ((((Formalism.L2.Theta.mt W h⁻¹).map (Formalism.L2.Theta.cA D)).transpose *
          (Formalism.BasicNotions.HSpace.gram W).map (Formalism.L2.Theta.incA D) * Formalism.L2.Theta.mt W h⁻¹) *
          y.map (Formalism.L2.Theta.incA D)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu]

theorem pch_rat (ψ : AddChar (AF D.host.F) ℂ) {n : ℕ} (x : hermA D n) (T : HermE D n) :
    pch ψ x.1 (rat T.1) = GlobalTheory.CompanionTheory.SiegelND.pairH ψ (GlobalTheory.CompanionTheory.HermPoisson.ofHermE T).1 x := by
  show ψ (GlobalTheory.StdUnn.halfTr (Matrix.trace (x.1 * rat T.1))) =
    ψ (GlobalTheory.StdUnn.halfTr (Matrix.trace (rat T.1 * x.1)))
  rw [Matrix.trace_mul_comm]

theorem conj_eq_inv {z : ℂ} (hz : ‖z‖ = 1) : conj z = z⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
  simp

variable {W : HSp D} {n : ℕ} {m : Measure (GA D W)} {𝓕 : Set (GA D W)} {Ψ : Mx D W.rank n → ℂ}

theorem cont_term (hΨ : Continuous Ψ) (y : Matrix (Fin W.rank) (Fin n) D.host.E) :
    Continuous fun h : GA D W => Ψ (mm (mt W h⁻¹) (rat y)) := by
  exact hΨ.comp ((GlobalTheory.RealWeil.continuous_mt W).2.matrix_mul continuous_const)

def co (W : HSp D) (m : Measure (GA D W)) (𝓕 : Set (GA D W)) (Ψ : Mx D W.rank n → ℂ)
    (y : Matrix (Fin W.rank) (Fin n) D.host.E) : ℂ :=
  ∫ h in 𝓕, Ψ (mm (mt W h⁻¹) (rat y)) ∂m

theorem lint_fin (hvol : m 𝓕 < ⊤) (hΨ : Continuous Ψ) {C : ℝ≥0}
    (hC : ∀ h : GA D W, ∑' x : Sp W n, ‖Ψ (mm (mt W h⁻¹) (rat x.1))‖ₑ ≤ C) :
    ∑' y : Sp W n, ∫⁻ h in 𝓕, ‖Ψ (mm (mt W h⁻¹) (rat y.1))‖ₑ ∂m < ⊤ := by
  have hmeas : ∀ y : Sp W n, AEMeasurable (fun h : GA D W => ‖Ψ (mm (mt W h⁻¹) (rat y.1))‖ₑ)
      (m.restrict 𝓕) := fun y => (cont_term hΨ y.1).enorm.measurable.aemeasurable
  calc ∑' y : Sp W n, ∫⁻ h in 𝓕, ‖Ψ (mm (mt W h⁻¹) (rat y.1))‖ₑ ∂m
      = ∫⁻ h in 𝓕, ∑' y : Sp W n, ‖Ψ (mm (mt W h⁻¹) (rat y.1))‖ₑ ∂m :=
        (MeasureTheory.lintegral_tsum hmeas).symm
    _ ≤ ∫⁻ _ in 𝓕, (C : ℝ≥0∞) ∂m := MeasureTheory.lintegral_mono (fun h => hC h)
    _ = C * m 𝓕 := MeasureTheory.setLIntegral_const 𝓕 C
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hvol

theorem tsum_co_ne_top (hvol : m 𝓕 < ⊤) (hΨ : Continuous Ψ) {C : ℝ≥0}
    (hC : ∀ h : GA D W, ∑' x : Sp W n, ‖Ψ (mm (mt W h⁻¹) (rat x.1))‖ₑ ≤ C) :
    ∑' y : Sp W n, ‖co W m 𝓕 Ψ y.1‖ₑ ≠ ⊤ := by
  refine ne_top_of_le_ne_top (lint_fin hvol hΨ hC).ne (ENNReal.tsum_le_tsum (fun y => ?_))
  exact MeasureTheory.enorm_integral_le_lintegral_enorm _

theorem summable_co (hvol : m 𝓕 < ⊤) (hΨ : Continuous Ψ) {C : ℝ≥0}
    (hC : ∀ h : GA D W, ∑' x : Sp W n, ‖Ψ (mm (mt W h⁻¹) (rat x.1))‖ₑ ≤ C) :
    Summable fun y : Sp W n => ‖co W m 𝓕 Ψ y.1‖ := by
  have h := tsum_co_ne_top hvol hΨ hC
  simp only [enorm_eq_nnnorm] at h
  exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp h)

theorem exch (hvol : m 𝓕 < ⊤) (hΨ : Continuous Ψ) {C : ℝ≥0}
    (hC : ∀ h : GA D W, ∑' x : Sp W n, ‖Ψ (mm (mt W h⁻¹) (rat x.1))‖ₑ ≤ C) (c : Sp W n → ℂ) (hc : ∀ y, ‖c y‖ = 1) :
    ∫ h in 𝓕, ∑' y : Sp W n, c y * Ψ (mm (mt W h⁻¹) (rat y.1)) ∂m = ∑' y : Sp W n, c y * co W m 𝓕 Ψ y.1 := by
  have hf : ∀ y : Sp W n, MeasureTheory.AEStronglyMeasurable
      (fun h : GA D W => c y * Ψ (mm (mt W h⁻¹) (rat y.1))) (m.restrict 𝓕) :=
    fun y => (continuous_const.mul (cont_term hΨ y.1)).aestronglyMeasurable
  have hc' : ∀ y, ‖c y‖ₑ = 1 := fun y => by
    rw [← ofReal_norm, hc y, ENNReal.ofReal_one]
  have hf' : ∑' y : Sp W n, ∫⁻ h in 𝓕, ‖c y * Ψ (mm (mt W h⁻¹) (rat y.1))‖ₑ ∂m ≠ ⊤ := by
    simp_rw [enorm_mul, hc', one_mul]
    exact (lint_fin hvol hΨ hC).ne
  rw [MeasureTheory.integral_tsum hf hf']
  congr 1
  funext y
  rw [MeasureTheory.integral_const_mul]
  rfl

end PositivityTheory.Rg.Rsw.L.LThCoef

end
