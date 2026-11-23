import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmPActualCptOfOuter
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCfLast
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurableOfContinuousOnZero

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Meas

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def glueMapI (i : Fin (r + 1)) (c : Fin r → ℂ) (q : Cf r i × Mt k r) : (Fin r → ℂ) × Mx k r :=
  (glue i c q.1, Matrix.of q.2)

theorem glueMapI_continuous (i : Fin (r + 1)) (c : Fin r → ℂ) : Continuous (glueMapI (k := k) i c) := by
  refine Continuous.prodMk ?_ continuous_snd
  refine continuous_pi fun l => ?_
  by_cases h : i.val ≤ l.val
  · have e : (fun q : Cf r i × Mt k r => glue i c q.1 l) = fun q => q.1 ⟨l, h⟩ := by
      funext q; simp [glue, h]
    rw [e]; exact (continuous_apply _).comp continuous_fst
  · have e : (fun q : Cf r i × Mt k r => glue i c q.1 l) = fun _ => c l := by
      funext q; simp [glue, h]
    rw [e]; exact continuous_const

theorem measurableSet_glueMapI_DomR (i : Fin (r + 1)) (c : Fin r → ℂ) :
    MeasurableSet (glueMapI (k := k) i c ⁻¹' DomR k r z z') := by
  rw [DomR_eq, Set.preimage_inter]
  exact ((Formalism.FourierDecayAlt.P.Qx5.isOpen_OpR k r z z').preimage (glueMapI_continuous i c)).measurableSet.inter
    (((Formalism.FourierDecayAlt.P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage
      (glueMapI_continuous i c)).measurableSet

theorem pair_measurableI (i : Fin (r + 1)) (c : Fin r → ℂ) (Φ Ψ : RadSp k r z z' π π') :
    Measurable (fun q : Cf r i × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2))) := by
  have hmaps : Set.MapsTo (glueMapI (k := k) i c) (glueMapI (k := k) i c ⁻¹' DomR k r z z') (DomR k r z z') :=
    fun q hq => hq
  have hΦc := (radSp_continuousOn Φ).comp (glueMapI_continuous i c).continuousOn hmaps
  have hΨc := (radSp_continuousOn Ψ).comp (glueMapI_continuous i c).continuousOn hmaps
  refine measurable_of_continuousOn_zero (measurableSet_glueMapI_DomR i c)
    ((Formalism.FourierDecayAlt.P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn (hΦc.prodMk hΨc)) ?_
  intro q hq
  have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2) = 0 := radSp_zero_off Φ hq
  show B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2)) _ = 0
  rw [h0, Formalism.FourierDecayAlt.P.B6.hilbert_schmidt_inner_basis_sum]
  simp

theorem pairAt_measI (μ : Measure (Mt k r)) [SFinite μ] (i : Fin (r + 1)) (u v : RadSp k r z z' π π')
    (c : Fin r → ℂ) : StronglyMeasurable (fun c' : Cf r i => pairAt μ u v (glue i c c')) :=
  (pair_measurableI i c u v).stronglyMeasurable.integral_prod_right'

def wtI (i : Fin (r + 1)) (c' : Cf r i) : ℂ := ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ)

theorem wtI_measurable (i : Fin (r + 1)) : Measurable (wtI i) := by
  unfold wtI
  have e : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by rw [zpow_neg]; norm_cast
  simp_rw [e]
  exact Complex.measurable_ofReal.comp
    (Finset.measurable_prod _ fun l _ => ((measurable_norm.comp (measurable_pi_apply l)).pow_const 2).inv)

def LevelSquareIntegrable (μ : Measure (Mt k r)) (i : Fin (r + 1)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) : Prop :=
  Integrable (fun c' : Cf r i => wtI i c' * pairAt μ u u (glue i c c'))

theorem hsInner_self_ofRealI (A : Wq →L[ℂ] Wp) : B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (B.hsVec A)]
  push_cast
  rfl

theorem norm_pairAt_selfI (μ : Measure (Mt k r)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u u c‖ = ∫ g : Mt k r, ‖B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))‖ ∂μ := by
  unfold pairAt
  simp_rw [hsInner_self_ofRealI]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun g => by positivity)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]

theorem norm_pairAt_leI (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    {u v : RadSp k r z z' π π'} (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u v c‖ ≤ ‖pairAt μ u u c‖ + ‖pairAt μ v v c‖ := by
  rw [norm_pairAt_selfI, norm_pairAt_selfI]
  unfold pairAt
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_add (int_lc μ hμ hu hu c).norm (int_lc μ hμ hv hv c).norm]
  exact integral_mono (int_lc μ hμ hu hv c).norm ((int_lc μ hμ hu hu c).norm.add (int_lc μ hμ hv hv c).norm)
    fun g => norm_hs_le _ _

theorem int_crossI (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (i : Fin (r + 1))
    {u v : RadSp k r z z' π π'} (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ)
    (Iu : LevelSquareIntegrable μ i u c) (Iv : LevelSquareIntegrable μ i v c) :
    Integrable (fun c' : Cf r i => wtI i c' * pairAt μ u v (glue i c c')) := by
  refine (Iu.norm.add Iv.norm).mono'
    ((wtI_measurable i).aestronglyMeasurable.mul (pairAt_measI μ i u v c).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun c' => ?_)
  show ‖wtI i c' * pairAt μ u v (glue i c c')‖ ≤
    ‖wtI i c' * pairAt μ u u (glue i c c')‖ + ‖wtI i c' * pairAt μ v v (glue i c c')‖
  rw [norm_mul, norm_mul, norm_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_pairAt_leI μ hμ hu hv _) (norm_nonneg _)

end Meas

section Red

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem formIntOuter_of_l2I {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : Measure (Mt k r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (i : Fin (r + 1)) (u v : Ix S → RadSp k r z z' π π')
    (hu : ∀ a, u a ∈ lcSub k r z z' π π') (hv : ∀ a, v a ∈ lcSub k r z z' π π') (c : Fin r → ℂ)
    (Iu : ∀ a, LevelSquareIntegrable μ i (u a) c) (Iv : ∀ a, LevelSquareIntegrable μ i (v a) c) :
    Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ a, pairAt μ (u a) (v a) (glue i c c')) := by
  simp_rw [Finset.mul_sum]
  exact integrable_finsetSum _ fun a _ => int_crossI μ hμ i (hu a) (hv a) c (Iu a) (Iv a)

def HermitianSquareIntegrableAt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (i : Fin (P.r + 1)) : Prop :=
  ∀ c ∈ OmX P.r, (∀ u ∈ herKc S P z z' π π' L st l0 D i, LevelSquareIntegrable μ i u c) ∧
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ x : Ix S → RadSp P.k P.r z z' π π',
      InK (herKc S P z z' π π' L st l0 D i) x → ∀ a, LevelSquareIntegrable μ i (act (RRi L st i w) x a) c

def HermitianSquareIntegrableAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ i : Fin (P.r + 1), i.val < P.r → HermitianSquareIntegrableAt (S := S) P z z' π π' μ L st l0 D i

theorem outer_form_compact_of_square (h : HermitianSquareIntegrableAll) : FormIntOuterCpt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' w hw i c hc x y hx hy
  by_cases hi : i.val < P.r
  · have : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
    have hle := herKc_le_lc (S := S) (st := st) (l0 := l0) X hD.2.2.1
      (fun F Φ hF hΦ => jfCptLocAll Wp Wq P z z' π π' D F Φ hD.1 hz hz' hπ hπ' hF hΦ) i
    have hRR := RRi_lc X μ L st l0 hD i w hw.1.2.1
    have hu : ∀ a, act (RRi L st i w) x a ∈ lcSub P.k P.r z z' π π' := fun a =>
      (lcSub P.k P.r z z' π π').sum_mem fun b _ => (hRR a b).1 _ (hle (hx b))
    obtain ⟨hK, hR⟩ := h Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' i hi c hc
    exact formIntOuter_of_l2I μ hD.2.1 i _ y hu (fun a => hle (hy a)) c (hR w hw x hx) (fun a => hK _ (hy a))
  · have e : i = Fin.last P.r := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    subst e
    exact integrable_cf_last _

end Red

end Formalism.FourierDecayAlt.P5.HerD
