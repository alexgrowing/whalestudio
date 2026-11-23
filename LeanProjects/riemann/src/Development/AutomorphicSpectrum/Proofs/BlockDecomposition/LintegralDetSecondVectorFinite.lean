import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GodementJacquetMinusOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GodementJacquetMinusTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOnModulusPowBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralBoundedRegionDetPowLtTop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCoordinatesBoundedRegion
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SingInt

theorem rpow_bound {u v m R e α : ℝ} (hα1 : α ≤ 1) (he : 2 * α - 2 ≤ e) (hu : 0 < u) (hv : 0 < v)
    (hum : u ≤ m) (hvm : v ≤ m) (hmR : m ≤ R) :
    m ^ e ≤ |R| ^ (e + 2 - 2 * α) * (u ^ (α - 1) * v ^ (α - 1)) := by
  have hm : 0 < m := hu.trans_le hum
  have hsplit : m ^ e = m ^ (e + 2 - 2 * α) * (m ^ (α - 1) * m ^ (α - 1)) := by
    rw [← Real.rpow_add hm, ← Real.rpow_add hm]
    congr 1
    ring
  rw [hsplit]
  have h1 : m ^ (e + 2 - 2 * α) ≤ |R| ^ (e + 2 - 2 * α) :=
    Real.rpow_le_rpow hm.le (hmR.trans (le_abs_self R)) (by linarith)
  have h2 : m ^ (α - 1) ≤ u ^ (α - 1) := Real.rpow_le_rpow_of_nonpos hu hum (by linarith)
  have h3 : m ^ (α - 1) ≤ v ^ (α - 1) := Real.rpow_le_rpow_of_nonpos hv hvm (by linarith)
  have hp : 0 ≤ m ^ (α - 1) := Real.rpow_nonneg hm.le _
  exact mul_le_mul h1 (mul_le_mul h2 h3 hp (hp.trans h2)) (mul_nonneg hp hp)
    (Real.rpow_nonneg (abs_nonneg R) _)

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def Bl (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (R : ℝ) : Set F := {z | (modulus z : ℝ) ≤ R}

def Ib (R : ℝ) (z : F) : ℝ≥0∞ := (Bl F R).indicator 1 z

def Pw (e : ℝ) (z : F) : ℝ≥0∞ := ENNReal.ofReal ((modulus z : ℝ) ^ e)

def fT (R c t : ℝ) : GL (Fin 2) F → ℝ≥0∞ :=
  Set.indicator {g : GL (Fin 2) F | ∀ i j, (modulus (g.val i j) : ℝ) ≤ R}
    (fun g => ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ c * mx (e2r g) ^ (-t)))

theorem measurableSet_Bl (R : ℝ) : MeasurableSet (Bl F R) :=
  measurableSet_le measurable_modulus.coe_nnreal_real measurable_const

theorem measurable_Ib (R : ℝ) : Measurable (Ib R : F → ℝ≥0∞) :=
  measurable_one.indicator (measurableSet_Bl R)

theorem measurable_Pw (e : ℝ) : Measurable (Pw e : F → ℝ≥0∞) :=
  ENNReal.measurable_ofReal.comp (measurable_modulus.coe_nnreal_real.pow_const e)

theorem Pw_mul (e : ℝ) (q w : F) : Pw e (q * w) = ENNReal.ofReal ((modulus q : ℝ) ^ e) * Pw e w := by
  rw [Pw, Pw, modulus_mul, NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _),
    ENNReal.ofReal_mul (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]

theorem Pw_neg (e : ℝ) (z : F) : Pw e (-z) = Pw e z := by
  rw [Pw, Pw, GlobalTheory.CompanionTheory.GL2Coordinates.modulus_neg']

theorem Ib_of_mem {R : ℝ} {z : F} (h : z ∈ Bl F R) : Ib R z = 1 := by
  simp [Ib, Set.indicator_of_mem h]

theorem Ib_of_notMem {R : ℝ} {z : F} (h : z ∉ Bl F R) : Ib R z = 0 := by
  simp [Ib, Set.indicator_of_notMem h]

theorem half (μ : Measure F) [μ.IsAddHaarMeasure] (R e : ℝ) {p q : F} (hq : q ≠ 0)
    (hpq : (modulus p : ℝ) ≤ modulus q) :
    ∫⁻ b, ∫⁻ a, Ib R a * (Ib R b * Pw e (a * q - b * p)) ∂μ ∂μ ≤
      ENNReal.ofReal ((modulus q : ℝ) ^ e) * (∫⁻ z, (Bl F R).indicator (Pw e) z ∂μ) * μ (Bl F R) := by
  set A := ∫⁻ z, (Bl F R).indicator (Pw e) z ∂μ with hA
  set c := ENNReal.ofReal ((modulus q : ℝ) ^ e) with hc
  have hqp : (0 : ℝ) < modulus q := by exact_mod_cast modulus_pos hq
  have key : ∀ b, ∫⁻ a, Ib R a * (Ib R b * Pw e (a * q - b * p)) ∂μ ≤
      (Bl F R).indicator (fun _ => c * A) b := by
    intro b
    by_cases hb : b ∈ Bl F R
    · rw [Set.indicator_of_mem hb]
      set w := b * p / q with hw
      have hmw : (modulus w : ℝ) ≤ R := by
        have h0 : (modulus w : ℝ) = modulus b * (modulus p / modulus q) := by
          simp [hw, div_eq_mul_inv, modulus_mul, modulus_inv, mul_assoc]
        rw [h0]
        have h1 : (modulus p : ℝ) / modulus q ≤ 1 := (div_le_one hqp).2 hpq
        calc (modulus b : ℝ) * (modulus p / modulus q) ≤ (modulus b : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left h1 (NNReal.coe_nonneg _)
          _ ≤ R := by rw [mul_one]; exact hb
      calc ∫⁻ a, Ib R a * (Ib R b * Pw e (a * q - b * p)) ∂μ
          ≤ ∫⁻ a, c * (Bl F R).indicator (Pw e) (a - w) ∂μ := by
            refine lintegral_mono fun a => ?_
            by_cases ha : a ∈ Bl F R
            · have h1 : a - w ∈ Bl F R := by
                have h2 := GlobalTheory.CompanionTheory.LFCoords.modulus_add_le_max a (-w)
                rw [GlobalTheory.CompanionTheory.GL2Coordinates.modulus_neg'] at h2
                rw [Bl, Set.mem_setOf_eq, sub_eq_add_neg]
                exact h2.trans (max_le ha hmw)
              have h2 : a * q - b * p = q * (a - w) := by
                rw [hw]
                field_simp
              rw [Ib_of_mem ha, Ib_of_mem hb, Set.indicator_of_mem h1, h2, Pw_mul]
              simp [hc]
            · rw [Ib_of_notMem ha]
              simp
        _ = c * ∫⁻ a, (Bl F R).indicator (Pw e) (a - w) ∂μ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = c * A := by
            rw [lintegral_sub_right_eq_self (fun z => (Bl F R).indicator (Pw e) z) w]
    · rw [Set.indicator_of_notMem hb]
      simp [Ib_of_notMem hb]
  calc ∫⁻ b, ∫⁻ a, Ib R a * (Ib R b * Pw e (a * q - b * p)) ∂μ ∂μ
      ≤ ∫⁻ b, (Bl F R).indicator (fun _ => c * A) b ∂μ := lintegral_mono key
    _ = c * A * μ (Bl F R) := lintegral_indicator_const (measurableSet_Bl R) _

theorem both (μ : Measure F) [μ.IsAddHaarMeasure] (R e : ℝ) (r : Fin 2 → F) (h0 : r 0 ≠ 0)
    (h1 : r 1 ≠ 0) :
    ∫⁻ b, ∫⁻ a, Ib R a * (Ib R b * Pw e (a * r 1 - b * r 0)) ∂μ ∂μ ≤
      ENNReal.ofReal (mx r ^ e) * (∫⁻ z, (Bl F R).indicator (Pw e) z ∂μ) * μ (Bl F R) := by
  rcases le_total (modulus (r 0) : ℝ) (modulus (r 1)) with h | h
  · have hm : mx r = modulus (r 1) := max_eq_right h
    rw [hm]
    exact half μ R e h1 h
  · have hm : mx r = modulus (r 0) := max_eq_left h
    rw [hm]
    have hmeas : Measurable (Function.uncurry fun b a : F =>
        Ib R a * (Ib R b * Pw e (a * r 1 - b * r 0))) := by
      have h3 : Measurable fun p : F × F => p.2 * r 1 - p.1 * r 0 := by fun_prop
      exact ((measurable_Ib R).comp measurable_snd).mul
        (((measurable_Ib R).comp measurable_fst).mul ((measurable_Pw e).comp h3))
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    refine le_trans (le_of_eq ?_) (half μ R e h0 h)
    refine lintegral_congr fun a => lintegral_congr fun b => ?_
    rw [← Pw_neg e (a * r 1 - b * r 0), neg_sub, mul_left_comm]

theorem measurable_fT (R c t : ℝ) : Measurable (fT R c t : GL (Fin 2) F → ℝ≥0∞) := by
  have hS : MeasurableSet {g : GL (Fin 2) F | ∀ i j, (modulus (g.val i j) : ℝ) ≤ R} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_le (GlobalTheory.CompanionTheory.GLFinVol.measurable_entry i j).coe_nnreal_real measurable_const
  have hm : Measurable fun g : GL (Fin 2) F => mx (e2r g) := by
    have h0 : (fun g : GL (Fin 2) F => mx (e2r g)) =
        fun g => max (modulus (g.val 1 0) : ℝ) (modulus (g.val 1 1) : ℝ) := by
      funext g
      simp [mx, e2r]
    rw [h0]
    exact (GlobalTheory.CompanionTheory.GLFinVol.measurable_entry 1 0).coe_nnreal_real.max
      (GlobalTheory.CompanionTheory.GLFinVol.measurable_entry 1 1).coe_nnreal_real
  exact (ENNReal.measurable_ofReal.comp
    ((GlobalTheory.CompanionTheory.GLFinVol.measurable_detm.coe_nnreal_real.pow_const c).mul (hm.pow_const _))).indicator hS

open Classical in

theorem ext_le (R c t : ℝ) (r : Fin 2 → F) (b a : F) :
    Function.extend GlobalTheory.CompanionTheory.GJHaar.ch (GlobalTheory.CompanionTheory.GJHaar.rho * fT R c t) 0 (GlobalTheory.CompanionTheory.GJHaar.ent r b a) ≤
      if r 0 ∈ Bl F R ∧ r 1 ∈ Bl F R then
        ENNReal.ofReal (mx r ^ (-t)) * (Ib R a * (Ib R b * Pw (c - 1 - 1) (a * r 1 - b * r 0)))
      else 0 := by
  by_cases hX : ∃ g, GlobalTheory.CompanionTheory.GJHaar.ch g = GlobalTheory.CompanionTheory.GJHaar.ent r b a
  · obtain ⟨g, hg⟩ := hX
    have h00 : g.val 0 0 = a := by simpa [GlobalTheory.CompanionTheory.GJHaar.ch, GlobalTheory.CompanionTheory.GJHaar.ent] using congrFun hg (0, 0)
    have h01 : g.val 0 1 = b := by simpa [GlobalTheory.CompanionTheory.GJHaar.ch, GlobalTheory.CompanionTheory.GJHaar.ent] using congrFun hg (0, 1)
    have h10 : g.val 1 0 = r 0 := by simpa [GlobalTheory.CompanionTheory.GJHaar.ch, GlobalTheory.CompanionTheory.GJHaar.ent] using congrFun hg (1, 0)
    have h11 : g.val 1 1 = r 1 := by simpa [GlobalTheory.CompanionTheory.GJHaar.ch, GlobalTheory.CompanionTheory.GJHaar.ent] using congrFun hg (1, 1)
    rw [← hg, GlobalTheory.CompanionTheory.GJHaar.measurableEmbedding_ch.injective.extend_apply, Pi.mul_apply]
    by_cases hS : g ∈ {g : GL (Fin 2) F | ∀ i j, (modulus (g.val i j) : ℝ) ≤ R}
    · have ha : a ∈ Bl F R := h00 ▸ hS 0 0
      have hb : b ∈ Bl F R := h01 ▸ hS 0 1
      have hr0 : r 0 ∈ Bl F R := h10 ▸ hS 1 0
      have hr1 : r 1 ∈ Bl F R := h11 ▸ hS 1 1
      have hd : (g.val).det = a * r 1 - b * r 0 := by
        rw [Matrix.det_fin_two, h00, h01, h10, h11]
      have hdne : (g.val).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
      have he : e2r g = r := by
        funext j
        fin_cases j <;> simp [e2r, h10, h11]
      have hD : (0 : ℝ) < modulus (g.val).det := by exact_mod_cast modulus_pos hdne
      rw [if_pos ⟨hr0, hr1⟩, Ib_of_mem ha, Ib_of_mem hb, ← hd, fT, Set.indicator_of_mem hS, he,
        GlobalTheory.CompanionTheory.GJHaar.rho_eq, Pw, ← ENNReal.ofReal_coe_nnreal, one_mul, one_mul]
      have hm0 : 0 ≤ mx r ^ (-t) := by
        refine Real.rpow_nonneg ?_ _
        exact le_max_of_le_left (NNReal.coe_nonneg _)
      refine le_of_eq ?_
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hm0]
      congr 1
      rw [Real.rpow_sub_one hD.ne', Real.rpow_sub_one hD.ne']
      push_cast
      field_simp
    · rw [fT, Set.indicator_of_notMem hS, mul_zero]
      simp
  · rw [Function.extend_apply' _ _ _ hX]
    simp

end D

theorem lintegral_det_mx_lt_top : ForS fun F _ _ _ _ _ _ ψ => ∀ R c t : ℝ, 1 < c → 0 ≤ t → t < c →
    ∫⁻ g, Set.indicator {g : GL (Fin 2) F | ∀ i j, (modulus (g.val i j) : ℝ) ≤ R}
      (fun g => ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ c * mx (e2r g) ^ (-t))) g ∂LFS.hG ψ < ⊤ := by
  intro F _ _ _ _ _ _ ψ hψ R c t hc ht htc
  set μ := selfDualMeasure ψ with hμ
  have hf : Measurable (fT (F := F) R c t) := measurable_fT R c t
  have hE : Measurable (Function.extend GlobalTheory.CompanionTheory.GJHaar.ch (GlobalTheory.CompanionTheory.GJHaar.rho * fT (F := F) R c t)
      (0 : (Fin 2 × Fin 2 → F) → ℝ≥0∞)) :=
    GlobalTheory.CompanionTheory.GJHaar.measurableEmbedding_ch.measurable_extend
      (GlobalTheory.CompanionTheory.GJHaar.measurable_rho.mul hf) measurable_const
  change ∫⁻ g, fT R c t g ∂LFS.hG ψ < ⊤
  rw [GlobalTheory.CompanionTheory.GJHaar.lintegral_hG ψ _ hf, GlobalTheory.CompanionTheory.GJHaar.lintegral_ent ψ _ hE]
  set A := ∫⁻ z, (Bl F R).indicator (Pw (c - 1 - 1)) z ∂μ with hAdef
  have hA : A ≠ ⊤ := by
    have hi := GlobalTheory.CompanionTheory.GJPow.integrableOn_modulus_rpow F ψ hψ (c - 1) R (by linarith)
    rw [hAdef, lintegral_indicator (measurableSet_Bl R)]
    exact hi.integrable.lintegral_lt_top.ne
  have hV : μ (Bl F R) ≠ ⊤ := (GlobalTheory.CompanionTheory.GLFinVol.ball_lt_top μ R).ne
  have hAV : A * μ (Bl F R) ≠ ⊤ := ENNReal.mul_ne_top hA hV
  set α := min ((c - t) / 2) 1 with hαdef
  have hα : 0 < α := lt_min (by linarith) one_pos
  have hα1 : α ≤ 1 := min_le_right _ _
  have hα2 : α ≤ (c - t) / 2 := min_le_left _ _
  set e := -t + (c - 1 - 1) with he
  set C := |R| ^ (e + 2 - 2 * α) with hC
  let h : F → ℝ := (Bl F R).indicator fun y => (modulus y : ℝ) ^ (α - 1)
  have hh : Integrable h μ :=
    (integrable_indicator_iff (measurableSet_Bl R)).2
      (GlobalTheory.CompanionTheory.GJPow.integrableOn_modulus_rpow F ψ hψ α R hα)
  have hP : Integrable (fun r : Fin 2 → F => ∏ i, h (r i)) (LFS.vol2 ψ) := by
    unfold LFS.vol2
    exact Integrable.fintype_prod (fun _ => hh)
  have ae0 : ∀ᵐ r ∂LFS.vol2 ψ, r (0 : Fin 2) ≠ 0 := by
    have : LFS.vol2 ψ {r | r (0 : Fin 2) = 0} = 0 := by
      unfold LFS.vol2
      exact Measure.pi_hyperplane _ 0 0
    exact measure_eq_zero_iff_ae_notMem.1 this
  have hb : ∀ᵐ r ∂LFS.vol2 ψ,
      ∫⁻ b, ∫⁻ a, Function.extend GlobalTheory.CompanionTheory.GJHaar.ch (GlobalTheory.CompanionTheory.GJHaar.rho * fT (F := F) R c t) 0
        (GlobalTheory.CompanionTheory.GJHaar.ent r b a) ∂selfDualMeasure ψ ∂selfDualMeasure ψ ≤
      ENNReal.ofReal (C * ∏ i, h (r i)) * (A * μ (Bl F R)) := by
    filter_upwards [ae0, GlobalTheory.CompanionTheory.GJHaar.ae_ne ψ] with r h0 h1
    by_cases hr : r 0 ∈ Bl F R ∧ r 1 ∈ Bl F R
    · have hu0 : (0 : ℝ) < modulus (r 0) := by exact_mod_cast modulus_pos h0
      have hv0 : (0 : ℝ) < modulus (r 1) := by exact_mod_cast modulus_pos h1
      have hum : (modulus (r 0) : ℝ) ≤ mx r := le_max_left _ _
      have hvm : (modulus (r 1) : ℝ) ≤ mx r := le_max_right _ _
      have hmR : mx r ≤ R := max_le hr.1 hr.2
      have hm0 : 0 < mx r := hu0.trans_le hum
      have hbd := rpow_bound (e := e) hα1 (by rw [he]; linarith) hu0 hv0 hum hvm hmR
      have hprod : ∏ i, h (r i) = (modulus (r 0) : ℝ) ^ (α - 1) * (modulus (r 1) : ℝ) ^ (α - 1) := by
        rw [Fin.prod_univ_two]
        simp only [h]
        rw [Set.indicator_of_mem hr.1, Set.indicator_of_mem hr.2]
      calc ∫⁻ b, ∫⁻ a, Function.extend GlobalTheory.CompanionTheory.GJHaar.ch (GlobalTheory.CompanionTheory.GJHaar.rho * fT (F := F) R c t) 0
            (GlobalTheory.CompanionTheory.GJHaar.ent r b a) ∂selfDualMeasure ψ ∂selfDualMeasure ψ
          ≤ ∫⁻ b, ∫⁻ a, ENNReal.ofReal (mx r ^ (-t)) *
              (Ib R a * (Ib R b * Pw (c - 1 - 1) (a * r 1 - b * r 0))) ∂μ ∂μ := by
            refine lintegral_mono fun b => lintegral_mono fun a => ?_
            simpa only [if_pos hr] using ext_le R c t r b a
        _ = ENNReal.ofReal (mx r ^ (-t)) *
              ∫⁻ b, ∫⁻ a, Ib R a * (Ib R b * Pw (c - 1 - 1) (a * r 1 - b * r 0)) ∂μ ∂μ := by
            simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal (mx r ^ (-t)) *
              (ENNReal.ofReal (mx r ^ (c - 1 - 1)) * A * μ (Bl F R)) := by
            gcongr
            exact both μ R (c - 1 - 1) r h0 h1
        _ = ENNReal.ofReal (mx r ^ e) * (A * μ (Bl F R)) := by
            rw [he, Real.rpow_add hm0, ENNReal.ofReal_mul (Real.rpow_nonneg hm0.le _)]
            ring
        _ ≤ ENNReal.ofReal (C * ∏ i, h (r i)) * (A * μ (Bl F R)) := by
            rw [hprod]
            gcongr
    · have hz : ∀ b a, Function.extend GlobalTheory.CompanionTheory.GJHaar.ch (GlobalTheory.CompanionTheory.GJHaar.rho * fT (F := F) R c t) 0
          (GlobalTheory.CompanionTheory.GJHaar.ent r b a) = 0 := by
        intro b a
        have := ext_le R c t r b a
        rw [if_neg hr] at this
        exact le_antisymm this (by simp)
      simp [hz]
  refine lt_of_le_of_lt (lintegral_mono_ae hb) ?_
  rw [lintegral_mul_const' _ _ hAV]
  exact ENNReal.mul_lt_top (hP.const_mul C).lintegral_lt_top hAV.lt_top

end GlobalTheory.CompanionTheory.SingInt
