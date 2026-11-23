import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MeasurableBetGm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JReproB

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv ReciprocityTheory.ChartRestriction.DS.Mult1.Fold

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def orbL (D : RealPlaceData k r Wp Wp) (f : Mt k r → ℝ≥0∞) (x : Mt k r) : ℝ≥0∞ :=
  ∫⁻ p, f (Gm p x) ∂(D.μW.prod D.μN)

theorem fold_par (D : RealPlaceData k r Wp Wp) {ν : Measure (Mt k r)} (hν : Formalism.MainNotions.S.IsQuotMeas D.μG (muS D) ν)
    (f : Mt k r → ℝ≥0∞) (hf : Measurable f) : ∫⁻ x, f x ∂D.μG = ∫⁻ x, orbL D f x ∂ν := by
  rw [hν f hf]
  refine lintegral_congr fun x => ?_
  have hm : Measurable (fun s : Mt k r => f (fun i j => (Matrix.of s * Matrix.of x) i j)) :=
    hf.comp (measurable_rmul_mt (Matrix.of x))
  exact lintegral_map hm measurable_sP

theorem measurable_orbL (D : RealPlaceData k r Wp Wp) {f : Mt k r → ℝ≥0∞} (hf : Measurable f) : Measurable (orbL D f) := by
  have sW := sigmaFinite_of_haarOn D.haarW
  have sN := sigmaFinite_of_haarOn D.haarN
  exact (hf.comp measurable_Gm).lintegral_prod_left'

theorem orbL_inv (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) {f : Mt k r → ℝ≥0∞} (hf : Measurable f) {q : Mt k r × Mt k r}
    (hq : (Matrix.of q.1 : Mat k r) ∈ UWset k r D.z ∧ (Matrix.of q.2 : Mat k r) ∈ Nset k r) (x : Mt k r) :
    orbL D f (Gm q x) = orbL D f x := by
  have hT := shL_mp D (beFacts_of h D) hq.1 hq.2
  unfold orbL
  rw [← hT.lintegral_comp (f := fun p => f (Gm p x)) (hf.comp (measurable_Gm_fst x))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_S D] with p hp
  congr 1
  show (Matrix.of p.2 * Matrix.of p.1 : Mat k r) * ((Matrix.of q.2 * Matrix.of q.1) * Matrix.of x) =
    (Matrix.of p.2 * (Matrix.of p.1 * Matrix.of q.2 * (Matrix.of p.1)⁻¹)) * (Matrix.of p.1 * Matrix.of q.1) * Matrix.of x
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.of p.1 : Mat k r)⁻¹, gv_inv_mul hp.1.1, Matrix.one_mul]

theorem fold_inv (D : RealPlaceData k r Wp Wp) {ν : Measure (Mt k r)} (hν : Formalism.MainNotions.S.IsQuotMeas D.μG (muS D) ν)
    {u f : Mt k r → ℝ≥0∞} (hu : Measurable u) (hf : Measurable f)
    (hinv : ∀ p : Mt k r × Mt k r, (Matrix.of p.1 : Mat k r) ∈ UWset k r D.z ∧ (Matrix.of p.2 : Mat k r) ∈ Nset k r →
      ∀ x, u (Gm p x) = u x) :
    ∫⁻ x, u x * f x ∂D.μG = ∫⁻ x, u x * orbL D f x ∂ν := by
  rw [fold_par D hν (fun x => u x * f x) (hu.mul hf)]
  refine lintegral_congr fun x => ?_
  unfold orbL
  rw [← lintegral_const_mul (u x) (f := fun p => f (Gm p x)) (hf.comp (measurable_Gm_fst x))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_S D] with p hp
  rw [hinv p hp x]

def wt (x : Mt k r) : ℝ≥0∞ := bcPow (2 * AB k r) x

theorem measurable_wt : Measurable (wt (k := k) (r := r)) := bc_measurable_pow _

theorem gnInt_of (h : UnitaryGroupStructuralFacts) : GNIntSharp := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hGI, -⟩, -⟩ := id h
  exact hGI

theorem orb_wt_lt_top (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) :
    ∫⁻ x, orbL D wt x * wt x ∂D.μG < ∞ := by
  have hGL := gnLower_of h
  have hA := AB_nonneg k r
  have hK : 0 ≤ ReproducingFormula.KH k r := by unfold ReproducingFormula.KH; positivity
  set IS : ℝ≥0∞ := ∫⁻ p, ENNReal.ofReal (gN (sP p) ^ (-AB k r)) ∂(D.μW.prod D.μN) with hIS
  have hISlt : IS < ∞ := (stSInt h k r Wp D hD (AB k r) le_rfl).lintegral_lt_top
  have hG : ∫⁻ y : Mt k r, ENNReal.ofReal (gN (Matrix.of y) ^ (-AB k r)) ∂D.μG < ∞ :=
    gnInt_of h k r D.μG (AB k r) D.haarG le_rfl
  have hb : ∀ᵐ y ∂D.μG, orbL D wt y * wt y ≤
      (ENNReal.ofReal (ReproducingFormula.KH k r ^ AB k r) * IS) * ENNReal.ofReal (gN (Matrix.of y) ^ (-AB k r)) := by
    filter_upwards [ae_mem_of_haarOn D.haarG] with y hy
    have h1 : 1 ≤ gN (Matrix.of y : Mat k r) := hGL k r _ hy
    have hN : orbL D wt y ≤ ENNReal.ofReal ((ReproducingFormula.KH k r * gN (Matrix.of y)) ^ AB k r) * IS := by
      rw [hIS, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_mem_S D] with p hp
      have hs : sP p ∈ GV k r := gv_mul hp.2.1 hp.1.1
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc gN (sP p * Matrix.of y) ^ (-(2 * AB k r)) ≤ gN (sP p * Matrix.of y) ^ (-AB k r) :=
            Real.rpow_le_rpow_of_exponent_le (hGL k r _ (gv_mul hs hy)) (by linarith)
        _ ≤ gN (Matrix.of y : Mat k r)⁻¹ ^ AB k r * gN (sP p) ^ (-AB k r) := pow_mul_le hGL hs hy hA
        _ ≤ (ReproducingFormula.KH k r * gN (Matrix.of y)) ^ AB k r * gN (sP p) ^ (-AB k r) :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (bc_gN_nonneg _) (ReproducingFormula.gN_inv_le hy) hA)
              (Real.rpow_nonneg (bc_gN_nonneg _) _)
    have e : (ReproducingFormula.KH k r * gN (Matrix.of y : Mat k r)) ^ AB k r * gN (Matrix.of y : Mat k r) ^ (-(2 * AB k r)) =
        ReproducingFormula.KH k r ^ AB k r * gN (Matrix.of y : Mat k r) ^ (-AB k r) := by
      rw [Real.mul_rpow hK (by linarith), mul_assoc, ← Real.rpow_add (by linarith)]
      congr 2; ring
    calc orbL D wt y * wt y
        ≤ ENNReal.ofReal ((ReproducingFormula.KH k r * gN (Matrix.of y)) ^ AB k r) * IS * wt y := by gcongr
      _ = IS * ENNReal.ofReal ((ReproducingFormula.KH k r * gN (Matrix.of y : Mat k r)) ^ AB k r *
            gN (Matrix.of y : Mat k r) ^ (-(2 * AB k r))) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
          unfold wt bcPow; ring
      _ = _ := by rw [e, ENNReal.ofReal_mul (Real.rpow_nonneg hK _)]; ring
  refine lt_of_le_of_lt (lintegral_mono_ae hb) ?_
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hISlt.ne)]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hISlt) hG

theorem key (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) {ν : Measure (Mt k r)} (hν : Formalism.MainNotions.S.IsQuotMeas D.μG (muS D) ν)
    {u : Mt k r → ℝ≥0∞} (hu : Measurable u)
    (hinv : ∀ p : Mt k r × Mt k r, (Matrix.of p.1 : Mat k r) ∈ UWset k r D.z ∧ (Matrix.of p.2 : Mat k r) ∈ Nset k r →
      ∀ x, u (Gm p x) = u x) :
    ∫⁻ x, u x * wt x ∂D.μG ≤
      (∫⁻ x, u x ^ 2 ∂ν) ^ (1 / 2 : ℝ) * (∫⁻ x, orbL D wt x * wt x ∂D.μG) ^ (1 / 2 : ℝ) := by
  have hN := measurable_orbL D (measurable_wt (k := k) (r := r))
  rw [fold_inv D hν hu measurable_wt hinv,
    fold_inv D hν hN measurable_wt (fun p hp x => orbL_inv h D measurable_wt hp x)]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hu.aemeasurable hN.aemeasurable
  simp only [Pi.mul_apply, ENNReal.rpow_two] at hH
  simpa only [sq] using hH

def WeightedL1Bound (D : RealPlaceData k r Wp Wp) (X : SigData k r) (E : Submodule ℂ X.Hs) (B : X.Hs →ₗ[ℂ] Wp) : Prop :=
  ∃ C : ℝ, ∀ v ∈ E,
    Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-(2 * AB k r)) * ‖B (X.σ (Matrix.of y) v)‖) D.μG ∧
      ∫ y : Mt k r, gN (Matrix.of y) ^ (-(2 * AB k r)) * ‖B (X.σ (Matrix.of y) v)‖ ∂D.μG ≤ C * ‖v‖

theorem closed_GV (h : UnitaryGroupStructuralFacts) : IsClosed {y : Mt k r | (Matrix.of y : Mat k r) ∈ GV k r} := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCG, -⟩, -⟩ := id h
  exact (hCG k r).closed

theorem aesm_of_contOn (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) {F : Type} [NormedAddCommGroup F]
    [SecondCountableTopologyEither (Mt k r) F] {f : Mat k r → F} (hf : ContinuousOn f (GV k r)) :
    AEStronglyMeasurable (fun y : Mt k r => f (Matrix.of y)) D.μG := by
  have hf' : ContinuousOn (fun y : Mt k r => f (Matrix.of y)) {y : Mt k r | (Matrix.of y : Mat k r) ∈ GV k r} := hf
  have hm := hf'.aestronglyMeasurable (μ := D.μG) (closed_GV h).measurableSet
  have hae : ∀ᵐ y ∂D.μG, y ∈ {y : Mt k r | (Matrix.of y : Mat k r) ∈ GV k r} := ae_mem_of_haarOn D.haarG
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at hm

theorem weighted_l1_of_l2 (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) (X : SigData k r) (E : Submodule ℂ X.Hs)
    (B : X.Hs →ₗ[ℂ] Wp) {ν : Measure (Mt k r)} (hν : Formalism.MainNotions.S.IsQuotMeas D.μG (muS D) ν)
    (hE : ∀ g ∈ GV k r, ∀ v ∈ E, X.σ g v ∈ E)
    (hB : ∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, ∀ v ∈ E, B (X.σ (m * h) v) = psiD D m • D.π h (B v))
    (hc : ∀ v ∈ E, ContinuousOn (fun g => B (X.σ g v)) (GV k r))
    (hL : ∃ C : ℝ, ∀ v ∈ E, ∫⁻ x : Mt k r, ‖B (X.σ (Matrix.of x) v)‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (C * ‖v‖ ^ 2)) :
    WeightedL1Bound D X E B := by
  classical
  obtain ⟨C, hC⟩ := hL
  set KK : ℝ≥0∞ := (∫⁻ x, orbL D wt x * wt x ∂D.μG) ^ (1 / 2 : ℝ) with hKK
  have hKK' : KK ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (orb_wt_lt_top h D hD).ne).ne
  refine ⟨Real.sqrt |C| * KK.toReal, fun v hv => ?_⟩
  set G : Set (Mt k r) := {y | (Matrix.of y : Mat k r) ∈ GV k r} with hG
  set u : Mt k r → ℝ≥0∞ := G.piecewise (fun y => ‖B (X.σ (Matrix.of y) v)‖ₑ) (fun _ => 0) with hu
  have hc1 : ContinuousOn (fun y : Mt k r => B (X.σ (Matrix.of y) v)) G := hc v hv
  have hum : Measurable u :=
    (hc1.enorm).measurable_piecewise continuousOn_const (closed_GV h).measurableSet
  have hinv : ∀ p : Mt k r × Mt k r, (Matrix.of p.1 : Mat k r) ∈ UWset k r D.z ∧ (Matrix.of p.2 : Mat k r) ∈ Nset k r →
      ∀ x, u (Gm p x) = u x := by
    intro p hp x
    have hs : sP p ∈ GV k r := gv_mul hp.2.1 hp.1.1
    have e0 : (Matrix.of (Gm p x) : Mat k r) = sP p * Matrix.of x := rfl
    by_cases hx : x ∈ G
    · have hx' : Gm p x ∈ G := gv_mul hs hx
      have hxG : (Matrix.of x : Mat k r) ∈ GV k r := hx
      rw [hu, Set.piecewise_eq_of_mem _ _ _ hx', Set.piecewise_eq_of_mem _ _ _ hx, e0, X.rep.1.2 _ hs _ hxG,
        ContinuousLinearMap.comp_apply]
      have e1 := hB _ hp.1 _ hp.2 _ (hE _ hxG v hv)
      have e2 : ‖B (X.σ (sP p) (X.σ (Matrix.of x) v))‖ = ‖B (X.σ (Matrix.of x) v)‖ := by
        unfold sP; rw [e1, norm_smul, psiD_norm, one_mul, D.π_unitary _ hp.1]
      rw [← ofReal_norm, ← ofReal_norm, e2]
    · have hx' : Gm p x ∉ G := by
        intro hh
        apply hx
        have h2 : (sP p)⁻¹ * (sP p * Matrix.of x) ∈ GV k r := gv_mul (gv_inv hs) hh
        rwa [← Matrix.mul_assoc, gv_inv_mul hs, Matrix.one_mul] at h2
      rw [hu, Set.piecewise_eq_of_notMem _ _ _ hx', Set.piecewise_eq_of_notMem _ _ _ hx]
  have h2 : ∫⁻ x, u x ^ 2 ∂ν ≤ ENNReal.ofReal (Real.sqrt |C| * ‖v‖) ^ 2 := by
    refine le_trans (lintegral_mono fun x => ?_) ((hC v hv).trans ?_)
    · by_cases hx : x ∈ G
      · rw [hu, Set.piecewise_eq_of_mem _ _ _ hx]
      · rw [hu, Set.piecewise_eq_of_notMem _ _ _ hx]; simp
    · rw [← ENNReal.ofReal_pow (by positivity), mul_pow, Real.sq_sqrt (abs_nonneg C)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have h3 : ∫⁻ x, u x * wt x ∂D.μG ≤ ENNReal.ofReal (Real.sqrt |C| * ‖v‖) * KK := by
    refine (key h D hν hum hinv).trans ?_
    gcongr
    calc (∫⁻ x, u x ^ 2 ∂ν) ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal (Real.sqrt |C| * ‖v‖) ^ 2) ^ (1 / 2 : ℝ) := by gcongr
      _ = ENNReal.ofReal (Real.sqrt |C| * ‖v‖) := by
          rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num
  have hnn : 0 ≤ᵐ[D.μG] fun y : Mt k r => gN (Matrix.of y) ^ (-(2 * AB k r)) * ‖B (X.σ (Matrix.of y) v)‖ :=
    Filter.Eventually.of_forall fun y => mul_nonneg (Real.rpow_nonneg (bc_gN_nonneg _) _) (norm_nonneg _)
  have hm : AEStronglyMeasurable
      (fun y : Mt k r => gN (Matrix.of y) ^ (-(2 * AB k r)) * ‖B (X.σ (Matrix.of y) v)‖) D.μG :=
    (bc_gN_cont_mt.measurable.pow_const _).aestronglyMeasurable.mul (aesm_of_contOn h D (hc v hv)).norm
  have h4 : ∫⁻ y : Mt k r, ENNReal.ofReal (gN (Matrix.of y) ^ (-(2 * AB k r)) * ‖B (X.σ (Matrix.of y) v)‖) ∂D.μG =
      ∫⁻ x, u x * wt x ∂D.μG := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_of_haarOn D.haarG] with y hy
    rw [hu, Set.piecewise_eq_of_mem _ _ _ (show y ∈ G from hy),
      ENNReal.ofReal_mul (Real.rpow_nonneg (bc_gN_nonneg _) _), ofReal_norm, mul_comm]
    rfl
  have hfin : ENNReal.ofReal (Real.sqrt |C| * ‖v‖) * KK ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKK'
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal hnn).2 (by rw [h4]; exact lt_of_le_of_lt h3 hfin.lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm, h4]
  refine (ENNReal.toReal_mono hfin h3).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]; ring

end ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit
