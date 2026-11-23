import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanObjects
import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyTransition
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights
  GroundTheory.Heights₂.Heights.CP
open scoped ComplexConjugate ENNReal ContDiff Matrix

noncomputable section

variable {N : ℕ}

namespace ProjFS

lemma analyticAt_chartVec_apply (i m : Fin (N + 1)) (z : Fin N → ℂ) :
    AnalyticAt ℂ (fun w : Fin N → ℂ => chartVec i w m) z := by
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m
  · simp only [chartVec_self]; exact analyticAt_const
  · simp only [chartVec_succAbove]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).analyticAt z

lemma eventually_chartVec_ne {i m : Fin (N + 1)} {z : Fin N → ℂ} (h : chartVec i z m ≠ 0) :
    ∀ᶠ w in 𝓝 z, chartVec i w m ≠ 0 :=
  (analyticAt_chartVec_apply i m z).continuousAt.eventually_ne h

lemma analyticAt_transition (i j : Fin (N + 1)) {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0) :
    AnalyticAt ℂ (transition i j) z := by
  have : transition (N := N) i j = fun w k => chartVec i w (j.succAbove k) / chartVec i w j := by
    funext w k; rfl
  rw [this, analyticAt_pi_iff]
  intro k
  exact (analyticAt_chartVec_apply i _ z).div (analyticAt_chartVec_apply i j z) hz

lemma chartVec_chartCoord_chartInv {m j : Fin (N + 1)} {z : Fin N → ℂ} (hz : chartVec m z j ≠ 0) :
    chartVec j (chartCoord j (chartInv m z)) = (chartVec m z j)⁻¹ • chartVec m z :=
  chartVec_transition m j hz

lemma mem_chartDomain_iff {j k : Fin (N + 1)} {x : CP N} (hx : x ∈ chartDomain j) :
    x ∈ chartDomain k ↔ chartVec j (chartCoord j x) k ≠ 0 := by
  conv_lhs => rw [← chartInv_chartCoord j hx]
  rfl

lemma chartVec_chartCoord_of_mem {j k : Fin (N + 1)} {x : CP N} (hx : x ∈ chartDomain j)
    (hk : x ∈ chartDomain k) :
    chartVec k (chartCoord k x) =
      (chartVec j (chartCoord j x) k)⁻¹ • chartVec j (chartCoord j x) := by
  have h := (mem_chartDomain_iff hx).1 hk
  conv_lhs => rw [← chartInv_chartCoord j hx]
  exact chartVec_chartCoord_chartInv h

end ProjFS

open ProjFS

def projAtlas (N : ℕ) : FinHolAtlas N (CP N) where
  n := N + 1
  chart := chart
  cover := exists_mem_chartDomain
  holo j k := fun _z hz => analyticAt_transition j k hz.2

def tautologicalTransition (j k : Fin (N + 1)) (x : CP N) : ℂ := chartVec j (chartCoord j x) k

def tautologicalLineBundle (N : ℕ) : HolLineBundle (projAtlas N) where
  g := tautologicalTransition
  holo (j k m : Fin (N + 1)) := by
    intro z hz
    have hj : chartVec m z j ≠ 0 := hz.2.1
    have hk : chartVec m z k ≠ 0 := hz.2.2
    refine ((analyticAt_chartVec_apply m k z).div (analyticAt_chartVec_apply m j z) hj).congr ?_
    filter_upwards [eventually_chartVec_ne hj] with w hw
    change chartVec m w k / chartVec m w j = chartVec j (chartCoord j (chartInv m w)) k
    rw [chartVec_chartCoord_chartInv hw, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  ne_zero (j k : Fin (N + 1)) x hx := (mem_chartDomain_iff hx.1).1 hx.2
  cocycle (j k l : Fin (N + 1)) x hx := by
    have hk := (mem_chartDomain_iff hx.1.1).1 hx.1.2
    change chartVec j (chartCoord j x) l =
      chartVec j (chartCoord j x) k * chartVec k (chartCoord k x) l
    rw [chartVec_chartCoord_of_mem hx.1.1 hx.1.2, Pi.smul_apply, smul_eq_mul]
    field_simp

def fsPhi (j : Fin (N + 1)) (x : CP N) : ℝ := Real.log (normSq2 (chartVec j (chartCoord j x)))

lemma contDiff_normSq2_chartVec (m : Fin (N + 1)) :
    ContDiff ℝ ∞ (fun z : Fin N → ℂ => normSq2 (chartVec m z)) := by
  unfold normSq2
  exact ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_chartVec_apply ℝ m i)

def fsWeight (N : ℕ) : Weight (tautologicalLineBundle N) where
  φ := fsPhi
  smooth (j m : Fin (N + 1)) := by
    have hF : ContDiffOn ℝ ∞ (fun z : Fin N → ℂ =>
        Real.log ((‖chartVec m z j‖ ^ 2)⁻¹ * normSq2 (chartVec m z)))
        {z | chartVec m z j ≠ 0} := by
      refine ContDiffOn.log ?_ ?_
      · refine ContDiffOn.mul ?_ (contDiff_normSq2_chartVec m).contDiffOn
        refine ContDiffOn.inv ((contDiff_norm_sq ℝ).comp
          (contDiff_chartVec_apply ℝ m j)).contDiffOn ?_
        intro z hz; exact pow_ne_zero _ (norm_ne_zero_iff.2 hz)
      · intro z hz
        have h1 : 0 < ‖chartVec m z j‖ := norm_pos_iff.2 hz
        have h2 := normSq2_pos (chartVec_ne_zero m z)
        positivity
    refine (hF.mono fun z hz => hz.2).congr fun z hz => ?_
    have hz' : chartVec m z j ≠ 0 := hz.2
    change Real.log (normSq2 (chartVec j (chartCoord j (chartInv m z)))) = _
    rw [chartVec_chartCoord_chartInv hz', normSq2_smul, norm_inv, inv_pow]
  compat (j k : Fin (N + 1)) x hx := by
    have hk := (mem_chartDomain_iff hx.1).1 hx.2
    change Real.log (normSq2 (chartVec j (chartCoord j x))) =
      Real.log (normSq2 (chartVec k (chartCoord k x))) +
        Real.log (‖chartVec j (chartCoord j x) k‖ ^ 2)
    rw [chartVec_chartCoord_of_mem hx.1 hx.2, normSq2_smul, norm_inv]
    have hN := normSq2_pos (chartVec_ne_zero j (chartCoord j x))
    have hc : 0 < ‖chartVec j (chartCoord j x) k‖ := norm_pos_iff.2 hk
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp

def projMatrix : CP N → (Fin (N + 1) → Fin (N + 1) → ℂ) :=
  Projectivization.lift
    (fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} => fun i j => v.1 i * conj (v.1 j) / ((normSq2 v.1 : ℝ) : ℂ))
    (by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ t rfl
      have ht : t ≠ 0 := by rintro rfl; simp at ha
      have hb2 : ((normSq2 b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (normSq2_pos hb).ne'
      have htc : conj t ≠ 0 := (map_ne_zero _).2 ht
      funext i j
      simp only [Pi.smul_apply, smul_eq_mul, normSq2_smul, map_mul]
      rw [show ((‖t‖ ^ 2 * normSq2 b : ℝ) : ℂ) = t * conj t * ((normSq2 b : ℝ) : ℂ) by
        rw [Complex.mul_conj']; push_cast; ring]
      field_simp)

lemma continuous_projMatrix : Continuous (projMatrix (N := N)) := by
  rw [ProjTopology.continuous_iff]
  have h : projMatrix (N := N) ∘ Projectivization.mk' ℂ = fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} =>
      fun i j => v.1 i * conj (v.1 j) / ((normSq2 v.1 : ℝ) : ℂ) := by
    funext v; rfl
  rw [h]
  have hn : Continuous fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} => ((normSq2 v.1 : ℝ) : ℂ) := by
    unfold normSq2
    exact Complex.continuous_ofReal.comp (continuous_finset_sum _ fun m _ =>
      (continuous_norm.comp ((continuous_apply m).comp continuous_subtype_val)).pow 2)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Continuous.div (((continuous_apply i).comp continuous_subtype_val).mul
    (Complex.continuous_conj.comp ((continuous_apply j).comp continuous_subtype_val))) hn fun v => ?_
  exact_mod_cast (normSq2_pos v.2).ne'

lemma projMatrix_injective : Function.Injective (projMatrix (N := N)) := by
  intro x y hxy
  induction x using Projectivization.ind with
  | h v hv =>
  induction y using Projectivization.ind with
  | h w hw =>
  have e : ∀ i j, v i * conj (v j) / ((normSq2 v : ℝ) : ℂ) =
      w i * conj (w j) / ((normSq2 w : ℝ) : ℂ) := fun i j => congr_fun (congr_fun hxy i) j
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  have hv2 : ((normSq2 v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (normSq2_pos hv).ne'
  have hw2 : ((normSq2 w : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (normSq2_pos hw).ne'
  have hvj : conj (v j) ≠ 0 := (map_ne_zero _).2 hj
  have hwj : w j ≠ 0 := by
    intro h0
    have h1 := e j j
    rw [h0, zero_mul, zero_div, div_eq_zero_iff] at h1
    rcases h1 with h1 | h1
    · exact hj (by simpa [hvj] using h1)
    · exact hv2 h1
  have hwjc : conj (w j) ≠ 0 := (map_ne_zero _).2 hwj
  rw [Projectivization.mk_eq_mk_iff]
  refine ⟨Units.mk0 ((conj (w j) * ((normSq2 v : ℝ) : ℂ)) / (conj (v j) * ((normSq2 w : ℝ) : ℂ)))
    (div_ne_zero (mul_ne_zero hwjc hv2) (mul_ne_zero hvj hw2)), ?_⟩
  funext i
  have ei := e i j
  rw [div_eq_div_iff hv2 hw2] at ei
  simp only [Units.smul_mk0, Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hvj hw2)]
  linear_combination (-1 : ℂ) * ei

instance (N : ℕ) : T2Space (CP N) :=
  T2Space.of_injective_continuous projMatrix_injective continuous_projMatrix

namespace ProjFS

def logPot (z : Fin N → ℂ) : ℝ := Real.log (1 + normSqSum z)

lemma dNormSqSum_apply (a b : Fin N → ℂ) :
    dNormSqSum a b = ∑ m, 2 * (b m * conj (a m)).re := by
  simp [dNormSqSum, Complex.inner, mul_add]

def dNCLM : (Fin N → ℂ) →L[ℝ] ((Fin N → ℂ) →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := dNormSqSum
      map_add' := fun a b => by
        ext v
        simp only [dNormSqSum_apply, ContinuousLinearMap.add_apply, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [Pi.add_apply, map_add, mul_add, Complex.add_re]
      map_smul' := fun c a => by
        ext v
        simp only [dNormSqSum_apply, ContinuousLinearMap.smul_apply, RingHom.id_apply,
          smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
        rw [show v m * ((c : ℂ) * conj (a m)) = (c : ℂ) * (v m * conj (a m)) by ring,
          Complex.re_ofReal_mul]
        ring }

lemma coe_dNCLM : ⇑(dNCLM (N := N)) = dNormSqSum := rfl

lemma fderiv_logPot : fderiv ℝ (logPot (N := N)) = fun y => (1 + normSqSum y)⁻¹ • dNormSqSum y := by
  funext y
  exact (((hasFDerivAt_normSqSum y).const_add 1).log (one_add_normSqSum_pos y).ne').fderiv

lemma hasFDerivAt_inv_q (z : Fin N → ℂ) :
    HasFDerivAt (fun u : Fin N → ℂ => (1 + normSqSum u)⁻¹)
      ((-((1 + normSqSum z) ^ 2)⁻¹) • dNormSqSum z) z :=
  (hasDerivAt_inv (one_add_normSqSum_pos z).ne').comp_hasFDerivAt z
    ((hasFDerivAt_normSqSum z).const_add 1)

lemma fderiv2_logPot (z a b : Fin N → ℂ) :
    fderiv ℝ (fderiv ℝ logPot) z a b = (1 + normSqSum z)⁻¹ * dNormSqSum a b -
      ((1 + normSqSum z) ^ 2)⁻¹ * dNormSqSum z a * dNormSqSum z b := by
  rw [fderiv_logPot]
  have hd : HasFDerivAt (dNormSqSum (N := N)) dNCLM z := by
    rw [← coe_dNCLM]; exact dNCLM.hasFDerivAt
  have h2 : HasFDerivAt (fun y : Fin N → ℂ => (1 + normSqSum y)⁻¹ • dNormSqSum y)
      ((1 + normSqSum z)⁻¹ • dNCLM +
        ((-((1 + normSqSum z) ^ 2)⁻¹) • dNormSqSum z).smulRight (dNormSqSum z)) z :=
    (hasFDerivAt_inv_q z).smul hd
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, coe_dNCLM, smul_eq_mul]
  ring

lemma I_smul_single (i : Fin N) : Complex.I • (Pi.single i 1 : Fin N → ℂ) = Pi.single i Complex.I := by
  ext m; by_cases h : m = i
  · subst h; simp
  · simp [h]

theorem hessC_logPot (z : Fin N → ℂ) :
    hessC logPot z = (((1 + normSqSum z)⁻¹ : ℝ) : ℂ) •
      (1 - (((1 + normSqSum z)⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec (star z) z) := by
  ext i j
  simp only [hessC, fderiv2_logPot, I_smul_single, dNormSqSum_single, ← inv_pow]
  generalize (1 + normSqSum z)⁻¹ = r
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Complex.star_def, smul_eq_mul]
  by_cases h : i = j
  · subst h
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, sq] <;> ring
  · apply Complex.ext <;> simp [h, Complex.mul_re, Complex.mul_im, sq] <;> ring

theorem hessC_logPot_eq_chernCoeff (i : Fin (N + 1)) (z : Fin N → ℂ) :
    hessC logPot z = ((2 * Real.pi : ℝ) : ℂ) • chernCoeff i z := by
  rw [hessC_logPot, chernCoeff_eq_matrix, smul_smul]
  congr 1
  have hq := one_add_normSqSum_pos z
  have hpi := Real.pi_pos
  push_cast
  field_simp

theorem levi_logPot_nonneg (z w : Fin N → ℂ) : 0 ≤ levi logPot z w := by
  have h := re_star_dot_hessC (logPot (N := N)) z (star w)
  conv_rhs at h => rw [star_star]
  rw [← h, hessC_logPot_eq_chernCoeff 0, Matrix.smul_mulVec, dotProduct_smul,
    chernCoeff_quadForm, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hq := one_add_normSqSum_pos z
  have hpi := Real.pi_pos
  have hCS := norm_dotProduct_sq_le z (star w)
  have hS0 := normSqSum_nonneg z
  have hX : 0 ≤ ∑ j, ‖(star w) j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine mul_nonneg (by positivity) (mul_nonneg (by positivity) ?_)
  rw [sub_nonneg, inv_mul_le_iff₀ hq]
  nlinarith

end ProjFS

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
