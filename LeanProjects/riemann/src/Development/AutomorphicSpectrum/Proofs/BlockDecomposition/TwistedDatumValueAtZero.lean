import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitInducedRepresentationHypothesis
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2 lc)
open scoped NumberField.AdeleRing ValuativeRel
open Ad3.K.GL2LocalData

noncomputable section

namespace GlobalTheory.CompanionTheory.TwistZero

open GlobalTheory.CompanionTheory.SplitRep GlobalTheory.CompanionTheory.SplitPi

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem integral_scale_snd (χ : AddChar F Circle) {s : F} (hs : s ≠ 0) (G : F × F → ℂ) :
    ∫ u, G (u.1, s * u.2) ∂muS χ = (((modulus s : ℝ)⁻¹ : ℝ) : ℂ) * ∫ u, G u ∂muS χ := by
  have he1 : MeasurableEmbedding (fun x : F => s * x) := (Homeomorph.mulLeft₀ s hs).measurableEmbedding
  have hid : MeasurableEmbedding (id : F → F) := MeasurableEmbedding.id
  have he := hid.prodMap he1
  have hmap : Measure.map (Prod.map (id : F → F) (fun x : F => s * x)) (muS χ) =
      (modulus s)⁻¹ • muS χ := by
    rw [← Measure.map_prod_map _ _ measurable_id he1.measurable,
      map_mul_left_eq_smul _ hs, Measure.map_id, Measure.prod_smul_right]
  have h := he.integral_map (μ := muS χ) G
  rw [hmap, integral_smul_nnreal_measure] at h
  simp only [Prod.map, id] at h
  rw [← h, NNReal.smul_def, Complex.real_smul]
  push_cast
  ring_nf

theorem integral_norm_one (χ : AddChar F Circle) {s : F} (hs : s ≠ 0) (G : F × F → ℂ) :
    ∫ y, G (y * (s, s⁻¹)) ∂muS χ = ∫ y, G y ∂muS χ := by
  have h1 := integral_scale_fst χ hs (fun y : F × F => G (y.1, s⁻¹ * y.2))
  have h2 := integral_scale_snd χ (inv_ne_zero hs) G
  have e : ∀ y : F × F, y * ((s, s⁻¹) : F × F) = (s * y.1, s⁻¹ * y.2) := fun y => by
    ext <;> simp [mul_comm]
  simp only [e]
  rw [h1, h2, ← mul_assoc]
  have hM : ((modulus s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modulus_ne_zero hs
  rw [modulus_inv]
  push_cast
  field_simp

theorem rWS_zero_point (χ : AddChar F Circle) {m : Matrix (Fin 2) (Fin 2) F} (hm : m.det = 1) {s : F}
    (hs : s ≠ 0) (Ψ : F × F → ℂ) :
    rWS χ m (fun y => Ψ (y * (s, s⁻¹))) 0 = rWS χ m Ψ 0 := by
  by_cases hc : m 1 0 = 0
  · rw [rWS_zero χ hm hc, rWS_zero χ hm hc]
    simp
  · rw [rWS_ne χ hc, rWS_ne χ hc]
    congr 1
    have h := integral_norm_one χ hs (fun u : F × F =>
      (χ ((m 0 0 * ((0 : F × F).1 * (0 : F × F).2) + m 1 1 * (u.1 * u.2) -
        (u.1 * (0 : F × F).2 + u.2 * (0 : F × F).1)) / m 1 0) : ℂ) * Ψ u)
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have e : (u * ((s, s⁻¹) : F × F)).1 * (u * ((s, s⁻¹) : F × F)).2 = u.1 * u.2 := by
      simp only [Prod.fst_mul, Prod.snd_mul]
      field_simp
    simp only [e, Prod.fst_zero, Prod.snd_zero, mul_zero, zero_mul, add_zero]

theorem det_normal (g : GL (Fin 2) F) :
    (!![g.val 0 0 / (g.val).det, g.val 0 1; g.val 1 0 / (g.val).det, g.val 1 1] :
      Matrix (Fin 2) (Fin 2) F).det = 1 := by
  have hd : (g.val).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    exact this.ne_zero
  rw [Matrix.det_fin_two_of]
  rw [show g.val 0 0 / (g.val).det * g.val 1 1 - g.val 0 1 * (g.val 1 0 / (g.val).det) =
    (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) / (g.val).det by ring, ← Matrix.det_fin_two]
  exact div_self hd

theorem piS_zero (χ : AddChar F Circle) (c₁ : Fˣ →* ℂˣ) (g : GL (Fin 2) F) (u : Fˣ) (Φ : F × F → ℂ) :
    piS χ c₁ g (fun x => Φ (x * ((u : F), ((u⁻¹ : Fˣ) : F)))) 0 = piS χ c₁ g Φ 0 := by
  unfold piS
  congr 1
  have h := rWS_zero_point χ (det_normal g) u.ne_zero (fun y => Φ (y * ((g.val).det, 1)))
  simp only [rWS, rWm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h
  rw [Units.val_inv_eq_inv_val]
  rw [← h]
  congr 1
  funext y
  rw [mul_right_comm]

end Local

open GroundTheory.Global.AdicLiesOver in
theorem degreeOneEmbedding_zero {K : Type} [Field K] [NumberField K] (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] : dg1 v w (0 : K) = 0 := by
  have hinj : Function.Injective (algebraMap (Qv v) (Kv K w)) := (algebraMap (Qv v) (Kv K w)).injective
  have h := Function.leftInverse_invFun hinj 0
  simpa [dg1] using h

end GlobalTheory.CompanionTheory.TwistZero

namespace GlobalTheory.CompanionTheory.TwistZero

theorem val_tw_zero : ∀ (K : Type) [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl) (D : LM c v)
    (u : (Qv v)ˣ) (g : GL (Fin 2) (Qv v)), (D.tw u).val g 0 = D.val g 0 := by
  intro K _ _ c v D u g
  cases D with
  | sp w₁ w₂ Φ =>
    simp only [LM.tw, LM.val, degreeOneEmbedding_zero]
    exact piS_zero _ _ g u Φ
  | ns w σ η Φ => rfl

end GlobalTheory.CompanionTheory.TwistZero
