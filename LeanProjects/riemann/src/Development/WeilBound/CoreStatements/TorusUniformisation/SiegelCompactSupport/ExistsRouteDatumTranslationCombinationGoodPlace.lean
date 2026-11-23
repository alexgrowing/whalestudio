import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesSummableOnCovolumeDomain
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocallyConstantSplitOm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenAddSubgroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsThetaStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealPlaceSymplecticFormPositiveComplexStru
import Formalism.LocalToGlobal.IndefiniteReal.DatumLemmas

section
section
open MeasureTheory
open scoped ContDiff

noncomputable section
namespace PositivityTheory.Member.ZakTransform.Z

section Param

variable {P T : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T]

def dx {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : P × T → E) (p : P × T) : P →L[ℝ] E :=
  fderiv ℝ (fun x => a (x, p.2)) p.1

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T] in
theorem contDiff_dx {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {a : P × T → E} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (dx a) :=
  ContDiff.fderiv (f := fun (p : P × T) x => a (x, p.2)) (m := ∞)
    (ha.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))) contDiff_fst (by simp)

theorem hasFDerivAt_int {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (ν : Measure T)
    [IsFiniteMeasure ν] {S : Set T} (hS : IsCompact S) (hν : ∀ᵐ t ∂ν, t ∈ S) {a : P × T → E} (ha : ContDiff ℝ ∞ a) (x : P) :
    HasFDerivAt (fun x => ∫ t, a (x, t) ∂ν) (∫ t, dx a (x, t) ∂ν) x := by
  have hd := (contDiff_dx ha).continuous
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod hS).exists_bound_of_continuousOn hd.continuousOn
  obtain ⟨C', hC'⟩ := hS.exists_bound_of_continuousOn
    (ha.continuous.comp (continuous_const.prodMk continuous_id : Continuous fun t : T => (x, t))).continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.closedBall x 1) (F := fun x t => a (x, t))
    (F' := fun x t => dx a (x, t)) (bound := fun _ => C) (Metric.closedBall_mem_nhds x one_pos)
    (.of_forall fun y => (ha.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Integrable.of_bound (ha.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable C'
      (hν.mono fun t ht => hC' t ht))
    (hd.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (hν.mono fun t ht y hy => hC (y, t) ⟨hy, ht⟩) (integrable_const C) (.of_forall fun t y _ => ?_)
  exact ((ha.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) y).hasFDerivAt

end Param

section Torus

variable {V T : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T]
  (Γ : AddSubgroup T) [Countable Γ] (μ : Measure T) [μ.IsAddHaarMeasure] {𝓕 : Set T}
  (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) {S : Set T} (hS : IsCompact S) (hν : ∀ᵐ t ∂(μ.restrict 𝓕), t ∈ S)
  [IsFiniteMeasure (μ.restrict 𝓕)]

include h𝓕 hS hν

theorem int_fderiv_eq_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {g : T → E}
    (hg : ContDiff ℝ ∞ g) (hp : ∀ γ ∈ Γ, ∀ t, g (γ + t) = g t) (v : T) : ∫ t in 𝓕, fderiv ℝ g t v ∂μ = 0 := by
  have ha : ContDiff ℝ ∞ fun p : ℝ × T => g (p.2 + p.1 • v) := hg.comp (contDiff_snd.add (contDiff_fst.smul contDiff_const))
  have h := hasFDerivAt_int (μ.restrict 𝓕) hS hν ha 0
  have e : (fun s : ℝ => ∫ t in 𝓕, g (t + s • v) ∂μ) = fun _ => ∫ t in 𝓕, g t ∂μ :=
    funext fun s => GlobalTheory.HeisOrtho.setIntegral_add_right Γ μ 𝓕 h𝓕 g hp _
  simp only [e] at h
  have h0 := h.unique (hasFDerivAt_const _ _)
  have hd := (contDiff_dx ha).continuous.comp (continuous_const.prodMk continuous_id : Continuous fun t : T => ((0 : ℝ), t))
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hd.continuousOn
  have h1 := ContinuousLinearMap.integral_apply
    (Integrable.of_bound (μ := μ.restrict 𝓕) hd.aestronglyMeasurable C (hν.mono fun t ht => hC t ht)) 1
  simp only [Function.comp_apply] at h1
  rw [h0, zero_apply] at h1
  rw [h1]
  refine integral_congr_ae (.of_forall fun t => ?_)
  have h2 : HasDerivAt (fun s : ℝ => t + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add t
  have h3 := ((hg.differentiable (by simp) (t + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2)
  simp only [zero_smul, add_zero] at h3
  exact h3.deriv.symm

def ch (B : V →L[ℝ] T →L[ℝ] ℝ) (l : V) (t : T) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (B l t : ℝ))

omit h𝓕 hS hν [FiniteDimensional ℝ V] [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T] in
theorem hasFDerivAt_ch (B : V →L[ℝ] T →L[ℝ] ℝ) (l : V) (t : T) :
    HasFDerivAt (ch B l) ((ch B l t * (2 * Real.pi * Complex.I)) • (Complex.ofRealCLM.comp (B l))) t := by
  have h := (((Complex.ofRealCLM.comp (B l)).hasFDerivAt (x := t)).const_mul (2 * Real.pi * Complex.I)).cexp
  rw [smul_smul] at h
  exact h

omit h𝓕 hS hν [FiniteDimensional ℝ V] [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T] in
theorem contDiff_ch (B : V →L[ℝ] T →L[ℝ] ℝ) (l : V) : ContDiff ℝ ∞ (ch B l) :=
  (contDiff_const.mul (Complex.ofRealCLM.comp (B l)).contDiff).cexp

omit h𝓕 hS hν [FiniteDimensional ℝ V] [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T] in
theorem norm_ch (B : V →L[ℝ] T →L[ℝ] ℝ) (l : V) (t : T) : ‖ch B l t‖ = 1 := by
  rw [ch, Complex.norm_exp]; simp

theorem decay_zero (B : V →L[ℝ] T →L[ℝ] ℝ) (hB : ∀ l, (∀ t, B l t = 0) → l = 0) {K : Set V} (hK : IsCompact K)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E] (k : ℕ) :
    ∀ a : V × T → E, ContDiff ℝ ∞ a → (∀ x, ∀ γ ∈ Γ, ∀ t, a (x, γ + t) = a (x, t)) →
      ∃ C, ∀ l, (∀ γ ∈ Γ, ∀ t, ch B l (γ + t) = ch B l t) → ∀ x ∈ K,
        ‖l‖ ^ k * ‖∫ t in 𝓕, ch B l t • a (x, t) ∂μ‖ ≤ C := by
  induction k with
  | zero =>
    intro a ha _
    obtain ⟨C, hC⟩ := (hK.prod hS).exists_bound_of_continuousOn ha.continuous.continuousOn
    refine ⟨C * (μ.restrict 𝓕).real Set.univ, fun l _ x hx => ?_⟩
    rw [pow_zero, one_mul]
    exact norm_integral_le_of_norm_le_const (hν.mono fun t ht => by
      rw [norm_smul, norm_ch, one_mul]; exact hC (x, t) ⟨hx, ht⟩)
  | succ k ih =>
    intro a ha hp
    let b := Module.finBasis ℝ T
    let L : V →ₗ[ℝ] (Fin (Module.finrank ℝ T) → ℝ) := LinearMap.pi fun i => ((B.flip (b i) : V →L[ℝ] ℝ) : V →ₗ[ℝ] ℝ)
    have hL : LinearMap.ker L = ⊥ := LinearMap.ker_eq_bot'.2 fun l hl => hB l fun t => by
      have : (B l : T →ₗ[ℝ] ℝ) = 0 := b.ext fun i => congrFun hl i
      exact LinearMap.congr_fun this t
    obtain ⟨A, -, hA⟩ := L.exists_antilipschitzWith hL
    have hA' : ∀ l, ‖l‖ ≤ A * ∑ i, |B l (b i)| := fun l => by
      refine (hA.le_mul_norm (map_zero L) l).trans (mul_le_mul_of_nonneg_left ?_ A.2)
      exact (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).2 fun i =>
        Finset.single_le_sum (f := fun i => |B l (b i)|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have hd : ∀ v, ContDiff ℝ ∞ fun p : V × T => fderiv ℝ (fun t => a (p.1, t)) p.2 v := fun v =>
      (ContDiff.fderiv (f := fun (p : V × T) t => a (p.1, t)) (m := ∞)
        (ha.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)) contDiff_snd (by simp)).clm_apply contDiff_const
    choose C hC using fun i => ih _ (hd (b i)) fun x γ hγ t => by
      simp only
      rw [← fderiv_comp_add_left]
      simp only [hp x γ hγ]
    refine ⟨A * ∑ i, C i, fun l hl x hx => ?_⟩
    have hax : ContDiff ℝ ∞ fun t => a (x, t) := ha.comp (contDiff_const.prodMk contDiff_id)
    have hint : ∀ g : T → E, Continuous g → Integrable g (μ.restrict 𝓕) := fun g hg => by
      obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hg.continuousOn
      exact Integrable.of_bound hg.aestronglyMeasurable C (hν.mono fun t ht => hC t ht)
    have key : ∀ v, |B l v| * ‖∫ t in 𝓕, ch B l t • a (x, t) ∂μ‖ ≤
        ‖∫ t in 𝓕, ch B l t • fderiv ℝ (fun t => a (x, t)) t v ∂μ‖ := fun v => by
      have h0 := int_fderiv_eq_zero Γ μ h𝓕 hS hν (g := fun t => ch B l t • a (x, t)) ((contDiff_ch B l).smul hax)
        (fun γ hγ t => by simp only [hl γ hγ, hp x γ hγ]) v
      have e : ∀ t, fderiv ℝ (fun t => ch B l t • a (x, t)) t v =
          ch B l t • fderiv ℝ (fun t => a (x, t)) t v +
            (2 * Real.pi * Complex.I * (B l v : ℝ) : ℂ) • (ch B l t • a (x, t)) := fun t => by
        rw [((hasFDerivAt_ch B l t).fun_smul (hax.differentiable (by simp) t).hasFDerivAt).fderiv]
        simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul, smul_smul]
        congr 2; ring
      simp only [e] at h0
      rw [integral_add (hint (fun t => ch B l t • fderiv ℝ (fun t => a (x, t)) t v) ((contDiff_ch B l).continuous.smul
          ((hd v).continuous.comp (continuous_const.prodMk continuous_id : Continuous fun t : T => (x, t)))))
        (hint (fun t => (2 * Real.pi * Complex.I * (B l v : ℝ) : ℂ) • (ch B l t • a (x, t)))
          (((contDiff_ch B l).continuous.smul hax.continuous).const_smul _)), integral_smul] at h0
      rw [eq_neg_of_add_eq_zero_left h0, norm_neg, norm_smul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      simp only [norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, Complex.norm_ofNat, mul_one,
        abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_gt_three, abs_nonneg (B l v)]
    calc _ ≤ ‖l‖ ^ k * (A * ∑ i, |B l (b i)|) * ‖∫ t in 𝓕, ch B l t • a (x, t) ∂μ‖ := by
          rw [pow_succ]; gcongr; exact hA' l
      _ = A * ∑ i, ‖l‖ ^ k * (|B l (b i)| * ‖∫ t in 𝓕, ch B l t • a (x, t) ∂μ‖) := by
          rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) A.2
          exact (mul_le_mul_of_nonneg_left (key _) (by positivity)).trans (hC i l hl x hx)

theorem decay (B : V →L[ℝ] T →L[ℝ] ℝ) (hB : ∀ l, (∀ t, B l t = 0) → l = 0) {K : Set V} (hK : IsCompact K)
    (Λ : Set V) (hΛ : ∀ x, ∃ l ∈ Λ, ∃ y ∈ K, x = y + l) (hl : ∀ l ∈ Λ, ∀ γ ∈ Γ, ∀ t, ch B l (γ + t) = ch B l t) (k n : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]
      (a : V × T → E), ContDiff ℝ ∞ a → (∀ x, ∀ γ ∈ Γ, ∀ t, a (x, γ + t) = a (x, t)) →
      (∀ l ∈ Λ, ∀ x t, a (x + l, t) = ch B l t • a (x, t)) →
      ∃ C, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => ∫ t in 𝓕, a (x, t) ∂μ) x‖ ≤ C := by
  induction n with
  | zero =>
    intro E _ _ _ _ _ a ha hp hq
    obtain ⟨C, hC⟩ := decay_zero Γ μ h𝓕 hS hν B hB hK k a ha hp
    obtain ⟨C₀, hC₀⟩ := decay_zero Γ μ h𝓕 hS hν B hB hK 0 a ha hp
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    refine ⟨2 ^ (k - 1) * (|R| ^ k * C₀ + C), fun x => ?_⟩
    obtain ⟨l, hlΛ, y, hy, rfl⟩ := hΛ x
    rw [norm_iteratedFDeriv_zero]
    simp only [hq l hlΛ]
    have h1 := hC l (hl l hlΛ) y hy
    have h2 := hC₀ l (hl l hlΛ) y hy
    rw [pow_zero, one_mul] at h2
    have h3 : ‖y + l‖ ^ k ≤ 2 ^ (k - 1) * (|R| ^ k + ‖l‖ ^ k) :=
      (pow_le_pow_left₀ (norm_nonneg _) ((norm_add_le _ _).trans
        (add_le_add_left ((hR y hy).trans (le_abs_self R)) _)) k).trans (add_pow_le (abs_nonneg R) (norm_nonneg l) k)
    refine (mul_le_mul_of_nonneg_right h3 (norm_nonneg _)).trans ?_
    rw [mul_assoc, add_mul]
    gcongr
  | succ n ih =>
    intro E _ _ _ _ _ a ha hp hq
    obtain ⟨C, hC⟩ := ih (V →L[ℝ] E) (dx a) (contDiff_dx ha) (fun x γ hγ t => by simp only [dx, hp _ γ hγ])
      (fun l hlΛ x t => by
        simp only [dx]
        rw [← fderiv_comp_add_right]
        simp only [hq l hlΛ]
        exact fderiv_fun_const_smul ((ha.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) x) _)
    refine ⟨C, fun x => ?_⟩
    rw [← norm_iteratedFDeriv_fderiv, show fderiv ℝ (fun x => ∫ t in 𝓕, a (x, t) ∂μ) = fun x => ∫ t in 𝓕, dx a (x, t) ∂μ from
      funext fun x => (hasFDerivAt_int _ hS hν ha x).fderiv]
    exact hC x

end Torus

section Cube

variable {ι : Type} [Fintype ι]

abbrev zl (ι : Type) [Fintype ι] : AddSubgroup (ι → ℝ) := (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup

abbrev cube (ι : Type) [Fintype ι] : Set (ι → ℝ) := ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)

instance countable_zl : Countable (zl ι) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance

def chi (m : ι → ℤ) (t : ι → ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (∑ i, m i * t i : ℝ))

end Cube

end PositivityTheory.Member.ZakTransform.Z
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ContDiff

noncomputable section
namespace PositivityTheory.Member.ZakTransform.Z

open NumberField.mixedEmbedding GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable (F : Type) [Field F] [NumberField F]

def re : mixedSpace F →+ AF F where
  toFun x := pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x) 0
  map_zero' := Prod.ext (map_zero _) rfl
  map_add' x y := Prod.ext (map_add _ x y) (add_zero _).symm

def fi : Af F →+ AF F where
  toFun x := pairA F 0 x
  map_zero' := rfl
  map_add' _ _ := Prod.ext (add_zero _).symm rfl

def Oh : Subring (Af F) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem (v.adicCompletionIntegers F)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem (v.adicCompletionIntegers F)
  neg_mem' ha v := neg_mem (ha v)

variable {F}

theorem re_mul_fi (x : mixedSpace F) (y : Af F) : re F x * fi F y = 0 := Prod.ext (mul_zero _) (zero_mul _)
theorem evI_re (x : mixedSpace F) : evI F (re F x) = x := RingEquiv.apply_symm_apply _ x
theorem re_add_fi (x : AF F) : re F (evI F x) + fi F x.2 = x :=
  Prod.ext ((add_zero _).trans (RingEquiv.symm_apply_apply _ _)) (zero_add _)
theorem continuous_fi : Continuous (fi F) := continuous_const.prodMk continuous_id

theorem psi_re {ψ : AddChar (AF F) ℂ} (hstd : IsStd ψ) (x : mixedSpace F) :
    ψ (re F x) = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedSpace F) x : ℝ)) := by
  rw [hstd.2.2 (re F x), evI_re]
  intro u hu
  rw [smul_eq_mul, ← re_add_fi u, hu, map_zero, zero_add, mul_comm, re_mul_fi]

theorem trace_emb (a : F) : Algebra.trace ℝ (mixedSpace F) (mixedEmbedding F a) = (Algebra.trace ℚ F a : ℚ) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (latticeBasis F), Algebra.trace_eq_matrix_trace (integralBasis F), Matrix.trace,
    Matrix.trace, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    latticeBasis_apply, ← map_mul, latticeBasis_repr_apply]

theorem lev {ι : Type} [Fintype ι] (W : Set (ι → Af F)) (hW : W ∈ nhds (0 : ι → Af F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ a : ι → Af F, (∀ i, a i ∈ Oh F) → N • a ∈ W := by
  classical
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, t, ht, hsub⟩ := hW
  choose M hM hMt using fun i => GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F (t i) (ht i)
  refine ⟨∏ i, M i, Finset.prod_pos fun i _ => hM i, fun a ha => hsub fun i _ => ?_⟩
  rw [Pi.smul_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_smul]
  exact hMt i _ (nsmul_mem (ha i) _)

variable {κ : Type} [Fintype κ]

def lv (F : Type) [Field F] [NumberField F] (κ : Type) (N : ℕ) : AddSubgroup (κ → Af F) where
  carrier := {x | ∃ a : κ → Af F, (∀ i, a i ∈ Oh F) ∧ x = N • a}
  zero_mem' := ⟨0, fun _ => zero_mem _, (smul_zero _).symm⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, fun i => add_mem (ha i) (hb i), (smul_add _ _ _).symm⟩
  neg_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, fun i => neg_mem (ha i), (smul_neg _ _).symm⟩

theorem lv_isOpen {N : ℕ} (hN : 0 < N) : IsOpen (lv F κ N : Set (κ → Af F)) := by
  refine AddSubgroup.isOpen_of_mem_nhds (g := 0) _ ?_
  have h := GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F N hN
  refine Filter.mem_of_superset (set_pi_mem_nhds Set.finite_univ fun i _ => h) fun x hx => ?_
  choose a ha e using fun i => hx i (Set.mem_univ i)
  exact ⟨a, ha, funext e⟩

theorem lv_isCompact (N : ℕ) : IsCompact (lv F κ N : Set (κ → Af F)) := by
  have h := (isCompact_univ_pi fun _ : κ => GlobalTheory.AdeleCocompact.isCompact_integral F).image
    (continuous_id.nsmul N : Continuous fun u : κ → Af F => N • u)
  convert h using 1
  ext x
  exact ⟨fun ⟨a, ha, e⟩ => ⟨a, fun i _ => ha i, e.symm⟩, fun ⟨a, ha, e⟩ => ⟨a, fun i => ha i trivial, e.symm⟩⟩

open Classical in

def ind (N : ℕ) (d x : κ → Af F) : ℂ := if x - d ∈ lv F κ N then 1 else 0

theorem ind_mem {N : ℕ} (hN : 0 < N) (d : κ → Af F) : ind N d ∈ SB (κ → Af F) := by
  classical
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : T2Space (Af F) := T2Space.of_injective_continuous (f := fi F) (fun x y h => congrArg Prod.snd h) continuous_fi
  have ho : IsClopen {x : κ → Af F | x - d ∈ lv F κ N} :=
    IsClopen.preimage (s := (lv F κ N : Set (κ → Af F))) ⟨(lv_isCompact N).isClosed, lv_isOpen hN⟩
      (continuous_id.sub continuous_const)
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, ?_⟩
  · by_cases h : x - d ∈ lv F κ N
    · exact ⟨_, ho.isOpen, h, fun y hy => by simp only [ind, if_pos h, if_pos (show y - d ∈ lv F κ N from hy)]⟩
    · exact ⟨_, ho.compl.isOpen, h, fun y hy => by simp only [ind, if_neg h, if_neg (show ¬ y - d ∈ lv F κ N from hy)]⟩
  · refine HasCompactSupport.of_support_subset_isCompact
      ((lv_isCompact N).image (continuous_id.add continuous_const : Continuous fun u : κ → Af F => u + d)) fun x hx => ?_
    by_cases h : x - d ∈ lv F κ N
    · exact ⟨_, h, sub_add_cancel _ _⟩
    · exact absurd (if_neg h) hx

abbrev al (ξ : κ → F) : κ → AF F := fun i => algebraMap F (AF F) (ξ i)

end PositivityTheory.Member.ZakTransform.Z
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ContDiff

noncomputable section
namespace PositivityTheory.Member.ZakTransform.Z

open NumberField.mixedEmbedding GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Coord

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

abbrev Ix (F : Type) [Field F] [NumberField F] : Type := Module.Free.ChooseBasisIndex ℤ (𝓞 F)

def Yl (N : ℕ) : (κ × Ix F → ℝ) →ₗ[ℝ] (κ → mixedSpace F) where
  toFun t i := ∑ j, t (i, j) • ((N : ℝ) • latticeBasis F j)
  map_add' s t := by funext i; simp [add_smul, Finset.sum_add_distrib]
  map_smul' c t := by funext i; simp [Finset.smul_sum, mul_smul]

open Classical in

def xi (N : ℕ) : (κ × Ix F → ℤ) →+ (κ → F) where
  toFun m i := ∑ j, (m (i, j) : F) * ((N : F)⁻¹ * (integralBasis F).traceDual j)
  map_zero' := by funext i; simp
  map_add' s t := by funext i; simp [add_mul, Finset.sum_add_distrib]

end Coord

def per {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (G : (κ → AF F) × (κ → AF F) → ℂ) (x y : κ → AF F) : ℂ := G (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y)))

end PositivityTheory.Member.ZakTransform.Z

namespace PositivityTheory.Member.ZakTransform

end PositivityTheory.Member.ZakTransform
end
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace PositivityTheory.Member.ZakTransform

section LocA
open Filter Topology

theorem L_interp {X : Type} [TopologicalSpace X] (A : Subalgebra ℂ (X → ℂ)) (hA : ∀ a ∈ A, IsLocallyConstant a)
    (hsep : ∀ x y, x ≠ y → ∃ a ∈ A, a x ≠ a y) {C : Set X} (hC : IsCompact C) {f : X → ℂ} (hf : IsLocallyConstant f) :
    ∃ g ∈ A, ∀ x ∈ C, g x = f x := by
  classical
  have hD : IsCompact ((C ×ˢ C) ∩ {p : X × X | f p.1 ≠ f p.2}) := by
    refine (hC.prod hC).inter_right ?_
    have : IsLocallyConstant fun p : X × X => f p.1 - f p.2 :=
      (hf.comp_continuous continuous_fst).sub (hf.comp_continuous continuous_snd)
    convert (this.isClopen_fiber 0).compl.isClosed using 1
    ext p; simp [sub_eq_zero]
  obtain ⟨t, ht⟩ := hD.elim_finite_subcover (fun a : A => {p : X × X | a.1 p.1 ≠ a.1 p.2}) (fun a => by
    have : IsLocallyConstant fun p : X × X => a.1 p.1 - a.1 p.2 :=
      ((hA _ a.2).comp_continuous continuous_fst).sub ((hA _ a.2).comp_continuous continuous_snd)
    convert (this.isClopen_fiber 0).compl.isOpen using 1
    ext p; simp [sub_eq_zero]) (fun p hp => by
    obtain ⟨a, ha, h⟩ := hsep p.1 p.2 fun e => hp.2 (by rw [e])
    exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, h⟩)
  let v : X → (t → ℂ) := fun x a => a.1.1 x
  have hv : ∀ x ∈ C, ∀ y ∈ C, v x = v y → f x = f y := fun x hx y hy e => by
    by_contra h
    obtain ⟨a, ha, h'⟩ := Set.mem_iUnion₂.1 (ht (show (x, y) ∈ _ from ⟨⟨hx, hy⟩, h⟩))
    exact h' (congrFun e ⟨a, ha⟩)
  have hfin : (v '' C).Finite := by
    have h1 : ∀ a : t, (a.1.1 '' C).Finite := fun a => by
      have : CompactSpace C := isCompact_iff_compactSpace.1 hC
      have := ((hA _ a.1.2).comp_continuous (continuous_subtype_val (p := (· ∈ C)))).range_finite
      rwa [Set.range_comp, Subtype.range_coe_subtype] at this
    refine (Set.Finite.pi' h1).subset ?_
    rintro _ ⟨x, hx, rfl⟩ a
    exact ⟨x, hx, rfl⟩
  have hδ : ∀ u w : t → ℂ, ∃ g ∈ A, u ≠ w → ∀ x, (v x = u → g x = 1) ∧ (v x = w → g x = 0) := fun u w => by
    by_cases h : u = w
    · exact ⟨0, zero_mem _, fun h' => (h' h).elim⟩
    obtain ⟨a, ha⟩ := Function.ne_iff.1 h
    refine ⟨(u a - w a)⁻¹ • (a.1.1 - algebraMap ℂ _ (w a)), A.smul_mem (sub_mem a.1.2 (A.algebraMap_mem _)) _,
      fun _ x => ⟨fun e => ?_, fun e => ?_⟩⟩
    · have : a.1.1 x = u a := congrFun e a
      simp [this, inv_mul_cancel₀ (sub_ne_zero.2 ha)]
    · have : a.1.1 x = w a := congrFun e a
      simp [this]
  choose δ hδA hδ using hδ
  have hrep : ∀ u, ∃ c, ∀ x ∈ C, v x = u → f x = c := fun u => by
    by_cases h : ∃ x ∈ C, v x = u
    · obtain ⟨y, hy, rfl⟩ := h
      exact ⟨f y, fun x hx e => hv x hx y hy e⟩
    · exact ⟨0, fun x hx e => (h ⟨x, hx, e⟩).elim⟩
  choose r hr using hrep
  refine ⟨∑ u ∈ hfin.toFinset, r u • ∏ w ∈ hfin.toFinset.erase u, δ u w,
    sum_mem fun u _ => A.smul_mem (prod_mem fun w _ => hδA u w) _, fun x hx => ?_⟩
  have hm : v x ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨x, hx, rfl⟩
  rw [Finset.sum_apply, Finset.sum_eq_single_of_mem _ hm]
  · rw [Pi.smul_apply, Finset.prod_apply, Finset.prod_eq_one fun w hw =>
      (hδ _ _ (Finset.ne_of_mem_erase hw).symm x).1 rfl, smul_eq_mul, mul_one]
    exact (hr _ x hx rfl).symm
  · intro u _ hu
    rw [Pi.smul_apply, Finset.prod_apply, Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hu.symm, hm⟩)
      ((hδ _ _ hu x).2 rfl), smul_zero]

theorem L_mul_mem {X : Type} [TopologicalSpace X] {a f : X → ℂ} (ha : IsLocallyConstant a) (hf : f ∈ SB X) :
    a * f ∈ SB X := ⟨ha.mul hf.1, hf.2.mul_left⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ψ : AddChar k ℂ} {κ : Type} [Fintype κ]

theorem L_lc (hc : Continuous ψ) : IsLocallyConstant ψ := by
  have := nonarch_field k
  exact isLocallyConstant_addChar ψ hc

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem L_nondeg (h1 : ψ ≠ 1) {x : κ → k} (hx : x ≠ 0) : ∃ y, ψ (x ⬝ᵥ y) ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  obtain ⟨a, ha⟩ := AddChar.ne_one_iff.mp h1
  refine ⟨Pi.single i (a / x i), ?_⟩
  rwa [dotProduct_single, mul_div_cancel₀ _ hi]

theorem L_exists_one : ∃ e ∈ SB (κ → k), e 0 = 1 := by
  have := GlobalTheory.SplitWeil.t2Space k
  let K : Set (κ → k) := Set.univ.pi fun _ => (𝒪[k] : Set k)
  have hKc : IsCompact K := isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_int k
  have hK : IsClopen K := ⟨hKc.isClosed, isOpen_set_pi Set.finite_univ fun _ _ => GlobalTheory.SplitWeil.isOpen_int k⟩
  exact ⟨K.indicator 1, ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hK).isLocallyConstant,
    HasCompactSupport.intro hKc fun x hx => Set.indicator_of_notMem hx _⟩,
    Set.indicator_of_mem (show (0 : κ → k) ∈ K from fun _ _ => zero_mem _) _⟩

variable [Invertible (2 : k)]

theorem L_schr_mem (hc : Continuous ψ) (w : (κ → k) × (κ → k)) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    schr ψ w φ ∈ SB (κ → k) :=
  L_mul_mem (a := fun x => ψ (x ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2))) (f := fun x => φ (x + w.1))
    ((L_lc hc).comp_continuous ((continuous_id.dotProduct continuous_const).add continuous_const))
    ⟨hφ.1.comp_continuous (continuous_add_right _), hφ.2.comp_homeomorph (Homeomorph.addRight w.1)⟩

def L_schrL (ψ : AddChar k ℂ) (w : (κ → k) × (κ → k)) : ((κ → k) → ℂ) →ₗ[ℂ] ((κ → k) → ℂ) where
  toFun := schr ψ w
  map_add' f g := by funext x; simp [schr, mul_add]
  map_smul' a f := by funext x; simp [schr, mul_left_comm]

theorem L_schur (hc : Continuous ψ) (h1 : ψ ≠ 1) (T : ((κ → k) → ℂ) →ₗ[ℂ] ((κ → k) → ℂ))
    (hT : ∀ w, ∀ φ ∈ SB (κ → k), T (schr ψ w φ) = schr ψ w (T φ)) : ∃ a : ℂ, ∀ φ ∈ SB (κ → k), T φ = a • φ := by
  obtain ⟨e, he, he0⟩ := L_exists_one (k := k) (κ := κ)
  let l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj (0 : κ → k) ∘ₗ T
  have hz : ∀ φ ∈ SB (κ → k), φ 0 = 0 → l φ = 0 := fun φ hφ h0 => by
    refine eq_zero_of_mul_invariant l (Set.range fun y : κ → k => fun u => ψ (u ⬝ᵥ y)) ?_ ?_ hφ ?_
    · rintro _ ⟨y, rfl⟩
      exact (L_lc hc).comp_continuous (continuous_id.dotProduct continuous_const)
    · rintro _ ⟨y, rfl⟩ φ hφ
      have e1 : (fun u => ψ (u ⬝ᵥ y)) * φ = schr ψ (0, y) φ := by funext u; simp [schr]
      show T _ 0 = T φ 0
      rw [e1, hT _ _ hφ]
      simp [schr]
    · intro u hu
      obtain ⟨y, hy⟩ := L_nondeg h1 (x := u) fun e => hu (e ▸ h0)
      exact ⟨_, ⟨y, rfl⟩, hy⟩
  refine ⟨l e, fun φ hφ => funext fun x => ?_⟩
  have h2 := L_schr_mem hc (x, 0) hφ
  have h3 := hz _ (sub_mem h2 (Submodule.smul_mem _ (φ x) he)) (by simp [schr, he0])
  rw [map_sub, map_smul, sub_eq_zero] at h3
  have h4 : l (schr ψ (x, 0) φ) = T φ x := by
    show T _ 0 = _
    rw [hT _ _ hφ]; simp [schr]
  rw [← h4, h3]; simp [mul_comm]

theorem L_irred (hc : Continuous ψ) (h1 : ψ ≠ 1) (N : Submodule ℂ ((κ → k) → ℂ)) (hN : N ≤ SB (κ → k))
    (hs : ∀ w, ∀ φ ∈ N, schr ψ w φ ∈ N) {φ₀ : (κ → k) → ℂ} (h0 : φ₀ ∈ N) (hne : φ₀ ≠ 0) : SB (κ → k) ≤ N := by
  classical
  let A : Subalgebra ℂ ((κ → k) → ℂ) :=
    { carrier := {a | IsLocallyConstant a ∧ ∀ φ ∈ N, a * φ ∈ N}
      mul_mem' := fun ha hb => ⟨ha.1.mul hb.1, fun φ hφ => by rw [mul_assoc]; exact ha.2 _ (hb.2 _ hφ)⟩
      add_mem' := fun ha hb => ⟨ha.1.add hb.1, fun φ hφ => by rw [add_mul]; exact add_mem (ha.2 _ hφ) (hb.2 _ hφ)⟩
      algebraMap_mem' := fun r => ⟨IsLocallyConstant.const r, fun φ hφ => N.smul_mem r hφ⟩ }
  have hmul : ∀ f, IsLocallyConstant f → ∀ φ ∈ N, f * φ ∈ N := fun f hf φ hφ => by
    obtain ⟨g, hg, h⟩ := L_interp A (fun a ha => ha.1) (fun x y hxy => by
      obtain ⟨z, hz⟩ := L_nondeg h1 (sub_ne_zero.2 hxy)
      refine ⟨fun u => ψ (u ⬝ᵥ z), ⟨(L_lc hc).comp_continuous (continuous_id.dotProduct continuous_const),
        fun φ hφ => ?_⟩, fun e => hz ?_⟩
      · have e1 : (fun u => ψ (u ⬝ᵥ z)) * φ = schr ψ (0, z) φ := by funext u; simp [schr]
        rw [e1]; exact hs _ _ hφ
      · have e' : ψ (x ⬝ᵥ z) = ψ (y ⬝ᵥ z) := e
        rw [sub_dotProduct, sub_eq_add_neg, AddChar.map_add_eq_mul, e', ← AddChar.map_add_eq_mul, add_neg_cancel,
          AddChar.map_zero_eq_one]) (hN hφ).2 hf
    have : f * φ = g * φ := funext fun x => by
      by_cases hx : φ x = 0
      · simp [hx]
      · simp [h x (subset_tsupport _ hx)]
    rw [this]; exact hg.2 _ hφ
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hne
  intro f hf
  obtain ⟨t, ht⟩ := (show IsCompact (tsupport f) from hf.2).elim_finite_subcover
    (fun a : κ → k => {x | schr ψ (a, 0) φ₀ x ≠ 0})
    (fun a => ((hN (hs (a, 0) _ h0)).1.isClopen_fiber 0).compl.isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x₀ - x, by simpa [schr] using hx₀⟩)
  let u : (κ → k) → ℂ := ∑ a ∈ t, star (schr ψ (a, 0) φ₀) * schr ψ (a, 0) φ₀
  have hu : u ∈ N := sum_mem fun a _ => hmul _ ((hN (hs (a, 0) _ h0)).1.comp star) _ (hs _ _ h0)
  have : f = (fun x => f x * (u x)⁻¹) * u := funext fun x => by
    by_cases hx : f x = 0
    · simp [hx]
    obtain ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport _ hx))
    have hux : u x ≠ 0 := by
      have e : u x = ((∑ a ∈ t, Complex.normSq (schr ψ (a, 0) φ₀ x) : ℝ) : ℂ) := by
        simp only [u, Finset.sum_apply, Pi.mul_apply, Pi.star_apply, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
        rfl
      rw [e, Complex.ofReal_ne_zero]
      exact (Finset.sum_pos' (f := fun a => Complex.normSq (schr ψ (a, 0) φ₀ x)) (fun _ _ => Complex.normSq_nonneg _)
        ⟨a, ha, Complex.normSq_pos.2 h⟩).ne'
    simp [hux]
  rw [this]
  exact hmul _ (hf.1.mul ((hN hu).1.comp (·⁻¹))) _ hu

theorem L_eventually_fix (hc : Continuous ψ) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), schr ψ w φ = φ := by
  have := nonarch_pi k κ
  obtain ⟨K, hK⟩ := HaarUniq.exists_invariant hφ
  have h1 : ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), w.1 ∈ K :=
    continuous_fst.continuousAt.preimage_mem_nhds (K.isOpen.mem_nhds K.zero_mem)
  have h2 : ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), ∀ x ∈ tsupport φ, ψ (x ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2)) = 1 := by
    apply IsCompact.eventually_forall_of_forall_eventually hφ.2
    intro x _
    have : IsLocallyConstant fun p : ((κ → k) × (κ → k)) × (κ → k) => ψ (p.2 ⬝ᵥ p.1.2 + ⅟(2 : k) * (p.1.1 ⬝ᵥ p.1.2)) :=
      (L_lc hc).comp_continuous ((continuous_snd.dotProduct continuous_fst.snd).add
        (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd)))
    simpa using this.eventually_eq (0, x)
  filter_upwards [h1, h2] with w hw1 hw2
  funext x
  rw [schr, hK _ hw1]
  by_cases hx : φ x = 0
  · simp [hx]
  · rw [hw2 x (subset_tsupport _ hx), one_mul]

theorem L_mem_of_fix (h1 : ψ ≠ 1) {f : (κ → k) → ℂ} (h : ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), schr ψ w f = f) :
    f ∈ SB (κ → k) := by
  classical
  have := GlobalTheory.SplitWeil.t2Space k
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, ?_⟩
  · have : Tendsto (fun y : κ → k => ((y - x, 0) : (κ → k) × (κ → k))) (𝓝 x) (𝓝 0) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    filter_upwards [this.eventually h] with y hy
    simpa [schr] using congrFun hy x
  · obtain ⟨a, ha⟩ := AddChar.ne_one_iff.mp h1
    have ha0 : a ≠ 0 := fun e => ha (by simp [e])
    have h2 : ∀ i, ∃ s : kˣ, ∀ c ∈ GlobalTheory.SplitWeil.cball s, schr ψ (0, Pi.single i c) f = f := fun i => by
      have : Tendsto (fun c : k => ((0, Pi.single i c) : (κ → k) × (κ → k))) (𝓝 0) (𝓝 0) :=
        Continuous.tendsto' (continuous_const.prodMk (continuous_single i)) _ _ (by simp)
      exact GlobalTheory.SplitWeil.exists_cball_subset (this.eventually h)
    choose s hs using h2
    refine HasCompactSupport.intro (isCompact_univ_pi fun i =>
      GlobalTheory.SplitWeil.isCompact_cball (Units.mk0 a ha0 / s i)) fun x hx => ?_
    by_contra hf
    refine hx fun i _ => ?_
    by_contra hi
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, not_le, Units.val_div_eq_div_val, Units.val_mk0, map_div₀] at hi
    have hs0 : 0 < valuation k (s i : k) := zero_lt_iff.2 (by simp)
    have hx0 : 0 < valuation k (x i) := lt_of_le_of_lt zero_le' hi
    have hx0' : x i ≠ 0 := fun e => by simp [e] at hx0
    have h3 := congrFun (hs i (a / x i) (by
      simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, map_div₀]
      rw [div_lt_iff₀ hs0] at hi
      rw [div_le_iff₀ hx0, mul_comm]; exact hi.le)) x
    simp only [schr, dotProduct_single, Pi.zero_apply, zero_mul, mul_zero, add_zero, mul_div_cancel₀ _ hx0'] at h3
    exact ha (mul_right_cancel₀ hf (h3.trans (one_mul _).symm))

end LocA

section LocB
open Filter Topology

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ψ : AddChar k ℂ} {κ : Type} [Fintype κ] [Invertible (2 : k)]

theorem L_form (hc : Continuous ψ) (s : ((κ → k) × (κ → k)) →ₗ[k] (κ → k) × (κ → k))
    (hs : ∀ y y', (s (0, y)).1 ⬝ᵥ (s (0, y')).2 - (s (0, y')).1 ⬝ᵥ (s (0, y)).2 = 0) :
    ∃ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ, (∃ φ ∈ SB (κ → k), l φ ≠ 0) ∧
      ∀ y, ∀ φ ∈ SB (κ → k), l (schr ψ (s (0, y)) φ) = l φ := by
  classical
  have := GlobalTheory.SplitWeil.t2Space k
  let m : (κ → k) →ₗ[k] (κ → k) × (κ → k) := s ∘ₗ LinearMap.inr k _ _
  let p : (κ → k) →ₗ[k] (κ → k) := LinearMap.fst k _ _ ∘ₗ m
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl (LinearMap.ker p)
  let r := Module.finrank k U
  let b : (Fin r → k) →ₗ[k] (κ → k) := U.subtype ∘ₗ (Module.finBasis k U).equivFun.symm.toLinearMap
  have hinj : LinearMap.ker (p ∘ₗ b) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    have h1 : b u ∈ LinearMap.ker p ⊓ U := ⟨hu, ((Module.finBasis k U).equivFun.symm u).2⟩
    rw [hU.inf_eq_bot, Submodule.mem_bot] at h1
    exact (Module.finBasis k U).equivFun.symm.map_eq_zero_iff.1 (Subtype.ext h1)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  have hg' : ∀ u, g (p (b u)) = u := fun u => LinearMap.congr_fun hg u
  have hdec : ∀ y, ∃ u η, m y = m (b u) + (0, η) := fun y => by
    obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.1 (hU.sup_eq_top.ge (Submodule.mem_top (x := y)))
    refine ⟨(Module.finBasis k U).equivFun ⟨c, hc'⟩, (m a).2, ?_⟩
    have e : b ((Module.finBasis k U).equivFun ⟨c, hc'⟩) = c := by simp only [b, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]; rfl
    rw [e, map_add, add_comm]
    congr 1
    exact Prod.ext ha rfl
  have cb : Continuous b := LinearMap.continuous_on_pi b
  have cm : Continuous m := LinearMap.continuous_on_pi m
  have cg : Continuous g := LinearMap.continuous_on_pi g
  let q : (Fin r → k) → k := fun u => ⅟(2 : k) * ((m (b u)).1 ⬝ᵥ (m (b u)).2)
  have cq : Continuous q := continuous_const.mul ((cm.comp cb).fst.dotProduct (cm.comp cb).snd)
  have ev : ∀ φ u, schr ψ (m (b u)) φ 0 = ψ (q u) * φ (p (b u)) := fun φ u => by simp [schr, q, p]
  borelize (Fin r → k)
  let ν : Measure (Fin r → k) := Measure.addHaar
  have hSB : ∀ φ ∈ SB (κ → k), (fun u => schr ψ (m (b u)) φ 0) ∈ SB (Fin r → k) := fun φ hφ => by
    simp only [ev]
    refine L_mul_mem (a := fun u => ψ (q u)) (f := fun u => φ (p (b u))) ((L_lc hc).comp_continuous cq)
      ⟨hφ.1.comp_continuous (cm.comp cb).fst, HasCompactSupport.intro (IsCompact.image hφ.2 cg) fun u hu => ?_⟩
    by_contra h
    exact hu ⟨_, subset_tsupport _ h, hg' u⟩
  have hint : ∀ φ ∈ SB (κ → k), Integrable (fun u => schr ψ (m (b u)) φ 0) ν := fun φ hφ =>
    (hSB φ hφ).1.continuous.integrable_of_hasCompactSupport (hSB φ hφ).2
  let l₀ : SB (κ → k) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ u, schr ψ (m (b u)) φ.1 0 ∂ν
      map_add' := fun φ φ' => by
        rw [← integral_add (hint _ φ.2) (hint _ φ'.2)]
        simp [schr, mul_add]
      map_smul' := fun a φ => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        simp [schr, mul_left_comm] }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend l₀
  have hl' : ∀ φ ∈ SB (κ → k), l φ = ∫ u, schr ψ (m (b u)) φ 0 ∂ν := fun φ hφ => LinearMap.congr_fun hl ⟨φ, hφ⟩
  refine ⟨l, ?_, fun y φ hφ => ?_⟩
  · obtain ⟨e, he, he0⟩ := L_exists_one (k := k) (κ := κ)
    have h1 : (fun x => ψ (-q (g x))) * (star e * e) ∈ SB (κ → k) :=
      L_mul_mem ((L_lc hc).comp_continuous (cq.comp cg).neg) (L_mul_mem (he.1.comp star) he)
    refine ⟨_, h1, ?_⟩
    have e2 : ∀ u, schr ψ (m (b u)) ((fun x => ψ (-q (g x))) * (star e * e)) 0 =
        ((Complex.normSq (e (p (b u))) : ℝ) : ℂ) := fun u => by
      rw [ev, Pi.mul_apply, hg', ← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, one_mul,
        Complex.normSq_eq_conj_mul_self]
      rfl
    have h3 := hSB _ h1
    rw [hl' _ h1]
    simp only [e2] at h3 ⊢
    rw [integral_complex_ofReal]
    have hcont : Continuous fun u => Complex.normSq (e (p (b u))) :=
      Complex.continuous_normSq.comp (he.1.continuous.comp (cm.comp cb).fst)
    have hcs : HasCompactSupport fun u => Complex.normSq (e (p (b u))) := h3.2.comp_left (g := Complex.re) rfl
    have := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := ν) hcs (fun _ => Complex.normSq_nonneg _)
      (x := 0) (by simp [he0])
    exact_mod_cast this.ne'
  · obtain ⟨u₀, η, h⟩ := hdec y
    rw [hl' _ hφ, hl' _ (L_schr_mem hc _ hφ), ← integral_add_right_eq_self (fun u => schr ψ (m (b u)) φ 0) u₀]
    refine integral_congr_ae (.of_forall fun u => ?_)
    have h1 : (m (b u)).1 ⬝ᵥ (m y).2 - (m y).1 ⬝ᵥ (m (b u)).2 = 0 := hs _ _
    have h2 : (m (y - b u₀)).1 ⬝ᵥ (m (b (u + u₀))).2 - (m (b (u + u₀))).1 ⬝ᵥ (m (y - b u₀)).2 = 0 := hs _ _
    have h3 : m (y - b u₀) = (0, η) := by rw [map_sub, h, add_sub_cancel_left]
    have h4 := schr_schr ψ (0, η) (m (b (u + u₀))) φ
    rw [h3] at h2
    rw [h2, mul_zero, AddChar.map_zero_eq_one, one_smul] at h4
    show schr ψ (m (b u)) (schr ψ (m y) φ) 0 = schr ψ (m (b (u + u₀))) φ 0
    rw [schr_schr, h1, mul_zero, AddChar.map_zero_eq_one, one_smul,
      show m (b u) + m y = (0, η) + m (b (u + u₀)) by rw [h, map_add, map_add]; abel, ← h4]
    simp [schr]

theorem L_half (hc : Continuous ψ) (h1 : ψ ≠ 1) (s : ((κ → k) × (κ → k)) →ₗ[k] (κ → k) × (κ → k))
    (hs : ∀ w w', (s w).1 ⬝ᵥ (s w').2 - (s w').1 ⬝ᵥ (s w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) :
    ∃ I : ((κ → k) → ℂ) →ₗ[ℂ] ((κ → k) → ℂ), (∀ φ ∈ SB (κ → k), I φ ∈ SB (κ → k)) ∧ (∃ φ ∈ SB (κ → k), I φ ≠ 0) ∧
      ∀ w, ∀ φ ∈ SB (κ → k), I (schr ψ (s w) φ) = schr ψ w (I φ) := by
  obtain ⟨l, ⟨φ₀, h0, hne⟩, hl⟩ := L_form hc s fun y y' => by rw [hs]; simp
  let I : ((κ → k) → ℂ) →ₗ[ℂ] ((κ → k) → ℂ) := LinearMap.pi fun x => l ∘ₗ L_schrL ψ (s (x, 0))
  have hI : ∀ φ x, I φ x = l (schr ψ (s (x, 0)) φ) := fun _ _ => rfl
  have key : ∀ w, ∀ φ ∈ SB (κ → k), I (schr ψ (s w) φ) = schr ψ w (I φ) := fun w φ hφ => funext fun x => by
    have e1 := hl w.2 _ (L_schr_mem hc (s (x + w.1, 0)) hφ)
    rw [schr_schr, hs, map_smul, ← map_add] at e1
    rw [hI, schr_schr, hs, map_smul, ← map_add, schr, hI, ← e1,
      show ((x, 0) : (κ → k) × (κ → k)) + w = (0, w.2) + (x + w.1, 0) by ext <;> simp, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [zero_dotProduct, dotProduct_zero, add_dotProduct]
    linear_combination (x ⬝ᵥ w.2) * (invOf_two_add_invOf_two (R := k))
  have cs : Continuous s := by
    have : (s : _ → _) = fun w => (s ∘ₗ LinearMap.inl k _ _) w.1 + (s ∘ₗ LinearMap.inr k _ _) w.2 := funext fun w => by
      simp [← map_add]
    rw [this]
    exact ((LinearMap.continuous_on_pi _).comp continuous_fst).add ((LinearMap.continuous_on_pi _).comp continuous_snd)
  refine ⟨I, fun φ hφ => L_mem_of_fix h1 ?_, ⟨φ₀, h0, fun e => hne ?_⟩, key⟩
  · filter_upwards [(cs.tendsto' 0 0 (map_zero s)).eventually (L_eventually_fix hc hφ)] with w hw
    rw [← key w φ hφ, hw]
  · have := congrFun e 0
    rw [hI, show ((0, 0) : (κ → k) × (κ → k)) = 0 from rfl, map_zero] at this
    refine Eq.trans ?_ this
    congr 1
    funext x
    simp [schr]

theorem L_svn (hc : Continuous ψ) (h1 : ψ ≠ 1) (s : ((κ → k) × (κ → k)) ≃ₗ[k] (κ → k) × (κ → k))
    (hs : ∀ w w', (s w).1 ⬝ᵥ (s w').2 - (s w').1 ⬝ᵥ (s w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) :
    ∃ I J : ((κ → k) → ℂ) →ₗ[ℂ] ((κ → k) → ℂ), (∀ φ ∈ SB (κ → k), I φ ∈ SB (κ → k) ∧ J (I φ) = φ) ∧
      (∀ φ ∈ SB (κ → k), J φ ∈ SB (κ → k) ∧ I (J φ) = φ) ∧
      ∀ w, ∀ φ ∈ SB (κ → k), I (schr ψ (s w) φ) = schr ψ w (I φ) := by
  obtain ⟨I, hI, hI0, kI⟩ := L_half hc h1 s.toLinearMap hs
  obtain ⟨J, hJ, ⟨f₀, hf₀, hJ0⟩, kJ⟩ := L_half hc h1 s.symm.toLinearMap fun w w' => by
    have := hs (s.symm w) (s.symm w')
    simp only [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  simp only [LinearEquiv.coe_coe] at kI kJ
  have inj : ∀ φ ∈ SB (κ → k), I φ = 0 → φ = 0 := fun φ hφ h => by
    by_contra hne
    obtain ⟨φ₀, h0, h0'⟩ := hI0
    refine h0' (L_irred hc h1 (SB (κ → k) ⊓ LinearMap.ker I) inf_le_left (fun w f hf => ⟨L_schr_mem hc _ hf.1, ?_⟩)
      ⟨hφ, h⟩ hne h0).2
    obtain ⟨w, rfl⟩ := s.surjective w
    show I _ = 0
    rw [kI _ _ hf.1, show I f = 0 from hf.2]
    funext x; simp [schr]
  obtain ⟨a, ha⟩ := L_schur hc h1 (I ∘ₗ J) fun w φ hφ => by
    show I (J _) = schr ψ w (I (J φ))
    rw [← kI _ _ (hJ _ hφ), ← kJ _ _ hφ, LinearEquiv.symm_apply_apply]
  have ha' : ∀ φ ∈ SB (κ → k), I (J φ) = a • φ := ha
  have ha0 : a ≠ 0 := fun e => hJ0 (inj _ (hJ _ hf₀) (by rw [ha' _ hf₀, e, zero_smul]))
  have hr : ∀ φ ∈ SB (κ → k), I ((a⁻¹ • J) φ) = φ := fun φ hφ => by
    rw [LinearMap.smul_apply, map_smul, ha' _ hφ, inv_smul_smul₀ ha0]
  have hm : ∀ φ ∈ SB (κ → k), (a⁻¹ • J) φ ∈ SB (κ → k) := fun φ hφ => Submodule.smul_mem _ _ (hJ _ hφ)
  refine ⟨I, a⁻¹ • J, fun φ hφ => ⟨hI _ hφ, sub_eq_zero.1 (inj _ (sub_mem (hm _ (hI _ hφ)) hφ) ?_)⟩,
    fun φ hφ => ⟨hm _ hφ, hr _ hφ⟩, kI⟩
  rw [map_sub, hr _ (hI _ hφ), sub_self]

end LocB

theorem svn {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
    (ψ : AddChar k ℂ) (hc : Continuous ψ) (h1 : ψ ≠ 1) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : (Matrix α β k × Matrix α β k) ≃ₗ[k] (α × β → k) × (α × β → k))
    (he : ∀ w w', (e w).1 ⬝ᵥ (e w').2 - (e w').1 ⬝ᵥ (e w).2 = trace (w.1 * w'.2ᵀ) - trace (w'.1 * w.2ᵀ)) :
    ∃ (I : ((α × β → k) → ℂ) →ₗ[ℂ] (Matrix α β k → ℂ)) (J : (Matrix α β k → ℂ) →ₗ[ℂ] ((α × β → k) → ℂ)),
      (∀ φ ∈ SB (α × β → k), I φ ∈ SB (Matrix α β k) ∧ J (I φ) = φ) ∧
      (∀ f ∈ SB (Matrix α β k), J f ∈ SB (α × β → k) ∧ I (J f) = f) ∧
      (∀ φ ∈ SB (α × β → k), ∀ Y₀ Y, I (schr ψ (e (Y₀, 0)) φ) Y = I φ (Y + Y₀)) ∧
      (∀ φ ∈ SB (α × β → k), ∀ Z Y, I (schr ψ (e (0, Z)) φ) Y = ψ (trace (Y * Zᵀ)) * I φ Y) := by
  let fl : Matrix α β k ≃ₗ[k] (α × β → k) := flat (Equiv.refl (α × β))
  have hd : ∀ X Y, fl X ⬝ᵥ fl Y = trace (X * Yᵀ) := flat_dot _
  let H : Matrix α β k ≃ₜ (α × β → k) :=
    { fl.toEquiv with
      continuous_toFun := continuous_pi fun p => continuous_id.matrix_elem p.1 p.2
      continuous_invFun := continuous_matrix fun i j => continuous_apply (i, j) }
  have hH : ∀ X, H X = fl X := fun _ => rfl
  obtain ⟨I, J, hI, hJ, kI⟩ := L_svn hc h1 ((fl.symm.prodCongr fl.symm).trans e) fun w w' => by
    simp only [LinearEquiv.trans_apply, he, LinearEquiv.prodCongr_apply, ← hd, LinearEquiv.apply_symm_apply]
  have kI' : ∀ Y Z, ∀ φ ∈ SB (α × β → k), I (schr ψ (e (Y, Z)) φ) = schr ψ (fl Y, fl Z) (I φ) := fun Y Z φ hφ => by
    rw [← kI _ _ hφ]; simp
  refine ⟨LinearMap.funLeft ℂ ℂ H ∘ₗ I, J ∘ₗ LinearMap.funLeft ℂ ℂ H.symm, fun φ hφ => ⟨?_, ?_⟩, fun f hf => ?_,
    fun φ hφ Y₀ Y => ?_, fun φ hφ Z Y => ?_⟩
  · exact ⟨(hI φ hφ).1.1.comp_continuous H.continuous, (hI φ hφ).1.2.comp_homeomorph H⟩
  · refine Eq.trans (congrArg J (funext fun x => ?_)) (hI φ hφ).2
    exact congrArg (I φ) (H.apply_symm_apply x)
  · have hf' : f ∘ H.symm ∈ SB (α × β → k) := ⟨hf.1.comp_continuous H.symm.continuous, hf.2.comp_homeomorph H.symm⟩
    refine ⟨(hJ _ hf').1, funext fun x => ?_⟩
    exact (congrFun (hJ _ hf').2 (H x)).trans (congrArg f (H.symm_apply_apply x))
  · show I _ (H Y) = I φ (H (Y + Y₀))
    rw [kI' _ _ _ hφ, hH, hH, map_add]; simp [schr]
  · show I _ (H Y) = _ * I φ (H Y)
    rw [kI' _ _ _ hφ, hH, ← hd]; simp [schr]

section LocC
open Filter Topology GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil hiding SB

theorem L_mobius {ι P : Type*} [Fintype ι] [PartialOrder P] (L : ι → P) (m G : ι → ℂ)
    (h : ∀ Λ, ∑ i, m i * (open Classical in if L i ≤ Λ then 1 else 0) = 0) (hG : ∀ i j, L i = L j → G i = G j) :
    ∑ i, m i * G i = 0 := by
  classical
  have key : ∀ (N : ℕ) (Λ : P), (Finset.univ.filter fun i => L i < Λ).card < N →
      ∑ i ∈ Finset.univ.filter fun i => L i = Λ, m i = 0 := by
    intro N
    induction N with
    | zero => intro Λ h; omega
    | succ N ih =>
      intro Λ hN
      have h1 : ∑ i ∈ Finset.univ.filter fun i => L i < Λ, m i = 0 := by
        rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ.filter fun i => L i < Λ).image L) (g := L)
          fun i hi => Finset.mem_image_of_mem L hi]
        refine Finset.sum_eq_zero fun Λ' hΛ' => ?_
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hΛ'
        have hj' := (Finset.mem_filter.1 hj).2
        rw [← ih (L j) (lt_of_lt_of_le (Finset.card_lt_card ⟨fun i hi => ?_, fun hs => ?_⟩) (Nat.le_of_lt_succ hN))]
        · refine Finset.sum_congr (Finset.ext fun i => ?_) fun _ _ => rfl
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => h.2, fun h => ⟨h ▸ hj', h⟩⟩
        · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2.trans hj'⟩
        · exact lt_irrefl _ (Finset.mem_filter.1 (hs hj)).2
      refine ((add_zero _).symm.trans (congrArg (_ + ·) h1.symm)).trans (Eq.trans ?_ (h Λ))
      simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h2 : L i = Λ
      · simp [h2]
      · by_cases h3 : L i < Λ
        · rw [if_pos h3.le, if_neg h2, if_pos h3, mul_one, zero_add]
        · rw [if_neg fun h => h3 (lt_of_le_of_ne h h2), if_neg h2, if_neg h3, mul_zero, zero_add]
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ.image L) (g := L) fun i hi => Finset.mem_image_of_mem L hi]
  refine Finset.sum_eq_zero fun Λ hΛ => ?_
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hΛ
  rw [Finset.sum_congr rfl fun i hi => by rw [hG i j (Finset.mem_filter.1 hi).2], ← Finset.sum_mul, key _ _ (Nat.lt_succ_self _),
    zero_mul]

theorem L_stable {K : Type} [Field K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) :
    ∃ C : Matrix (Fin n) (Fin n) K, (A + C * (1 - B * A)).det ≠ 0 := by
  let a := Matrix.toLin' A
  let nn := Matrix.toLin' (1 - B * A)
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (LinearMap.range a)
  have hd : Module.finrank K (LinearMap.ker a) = Module.finrank K Q := by
    have h1 := LinearMap.finrank_range_add_finrank_ker a
    have h2 := Submodule.finrank_add_eq_of_isCompl hQ
    omega
  let j := LinearEquiv.ofFinrankEq _ _ hd
  have hn : ∀ x, a x = 0 → nn x = x := fun x hx => by
    simp only [nn, map_sub, Matrix.toLin'_mul, Matrix.toLin'_one, LinearMap.sub_apply, LinearMap.comp_apply]
    rw [show Matrix.toLin' A x = 0 from hx]; simp
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.ker a).subtype (Submodule.ker_subtype _)
  let c := Q.subtype ∘ₗ j.toLinearMap ∘ₗ g
  refine ⟨LinearMap.toMatrix' c, fun h0 => ?_⟩
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have e : a x + c (nn x) = 0 := by
    rw [← hx, ← Matrix.toLin'_apply, map_add, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']; rfl
  have h1 : a x ∈ LinearMap.range a ⊓ Q := ⟨⟨x, rfl⟩, by
    rw [eq_neg_of_add_eq_zero_left e]; exact neg_mem (j (g (nn x))).2⟩
  rw [hQ.inf_eq_bot, Submodule.mem_bot] at h1
  rw [h1, zero_add, hn x h1] at e
  have h2 : g x = ⟨x, h1⟩ := LinearMap.congr_fun hg ⟨x, h1⟩
  have h3 : j (g x) = 0 := Subtype.ext e
  rw [j.map_eq_zero_iff, h2] at h3
  exact hx0 (congrArg Subtype.val h3)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem L_move {n d : ℕ} {Y Y' : Matrix (Fin n) (Fin d) k} (hY : Y.rank ≠ n)
    (h : Submodule.span 𝒪[k] (Set.range Y.row) = Submodule.span 𝒪[k] (Set.range Y'.row)) :
    ∃ M : Matrix (Fin n) (Fin n) k, (∀ i j, M i j ∈ 𝒪[k]) ∧ M.det = 1 ∧ M * Y = Y' := by
  have hA : ∀ {Y Y' : Matrix (Fin n) (Fin d) k}, Submodule.span 𝒪[k] (Set.range Y.row) =
      Submodule.span 𝒪[k] (Set.range Y'.row) → ∃ A : Matrix (Fin n) (Fin n) 𝒪[k], A.map (algebraMap 𝒪[k] k) * Y = Y' :=
    fun {Y Y'} h => by
      have : ∀ i, ∃ c : Fin n → 𝒪[k], ∑ j, c j • Y.row j = Y'.row i := fun i =>
        (Submodule.mem_span_range_iff_exists_fun _).1 (h ▸ Submodule.subset_span ⟨i, rfl⟩)
      choose c hc using this
      refine ⟨Matrix.of c, Matrix.ext fun i l => ?_⟩
      have := congrFun (hc i) l
      rw [Finset.sum_apply] at this
      exact this
  obtain ⟨A, hA1⟩ := hA h
  obtain ⟨B, hB1⟩ := hA h.symm
  let π := IsLocalRing.residue 𝒪[k]
  obtain ⟨C', hC'⟩ := L_stable (A.map π) (B.map π)
  choose l hl using IsLocalRing.residue_surjective (R := 𝒪[k])
  let K := A + C'.map l * (1 - B * A)
  have hK : IsUnit K.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have : (C'.map l).map π = C' := Matrix.ext fun i j => hl _
    have e : π.mapMatrix K = A.map π + C' * (1 - B.map π * A.map π) := by
      simp only [K, map_add, map_mul, map_sub, map_one]
      simp only [RingHom.mapMatrix_apply, this]
    rwa [e]
  have hKY : K.map (algebraMap 𝒪[k] k) * Y = Y' := by
    have : K.map (algebraMap 𝒪[k] k) = A.map (algebraMap 𝒪[k] k) + (C'.map l).map (algebraMap 𝒪[k] k) *
        (1 - B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k)) := by
      simp only [K, ← RingHom.mapMatrix_apply, map_add, map_mul, map_sub, map_one]
    rw [this, Matrix.add_mul, Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_assoc, hA1, hB1, Matrix.one_mul, sub_self,
      Matrix.mul_zero, add_zero]
  obtain ⟨p, hp0, hp⟩ : ∃ p : Fin n → k, p ≠ 0 ∧ p ᵥ* Y = 0 := by
    by_contra hc
    push Not at hc
    apply hY
    have hli : LinearIndependent k Y.row := Fintype.linearIndependent_iff.2 fun c hc' => by
      by_contra hi
      exact hc c (fun e => hi fun i => congrFun e i) (by rw [vecMul_eq_sum]; exact hc')
    rw [rank_eq_finrank_span_row, finrank_span_eq_card hli, Fintype.card_fin]
  obtain ⟨i₁, hi₁⟩ := Function.ne_iff.1 hp0
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => valuation k (p i)) ⟨i₁, Finset.mem_univ _⟩
  have hv : 0 < valuation k (p i) := lt_of_lt_of_le (zero_lt_iff.2 (by simpa using hi₁)) (hi i₁ (Finset.mem_univ _))
  have hpi : p i ≠ 0 := fun e => by simp [e] at hv
  let p' : Fin n → 𝒪[k] := fun j => ⟨p j / p i, by
    rw [Valuation.mem_integer_iff, map_div₀, div_le_one₀ hv]; exact hi j (Finset.mem_univ _)⟩
  have hp1 : p' i = 1 := Subtype.ext (div_self hpi)
  let K' : Matrix (Fin n) (Fin n) 𝒪[k] := 1 + vecMulVec (Pi.single i (((hK.unit⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) - 1)) p'
  have hK' : K'.det = (hK.unit⁻¹ : 𝒪[k]ˣ) := by
    simp only [K']
    rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_single, hp1]; ring
  refine ⟨(K * K').map (algebraMap 𝒪[k] k), fun i j => ((K * K') i j).2, ?_, ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_mul, hK', IsUnit.mul_val_inv, map_one]
  · rw [Matrix.map_mul, Matrix.mul_assoc, ← hKY]
    congr 1
    ext a b
    have h0 := congrFun hp b
    simp only [vecMul, dotProduct, Pi.zero_apply] at h0
    have h1 : ∑ x, p x / p i * Y x b = 0 := by
      simp only [div_mul_eq_mul_div, ← Finset.sum_div, h0, zero_div]
    simp only [K', ← RingHom.mapMatrix_apply, map_add, map_one, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply,
      add_eq_left]
    simp only [Matrix.mul_apply, RingHom.mapMatrix_apply, map_apply, vecMulVec_apply, map_mul, mul_assoc,
      ← Finset.mul_sum]
    exact mul_eq_zero_of_right _ h1

theorem L_avg {n d : ℕ} (S : Finset (Matrix (Fin n) (Fin d) k → ℂ)) (hS : ∀ f ∈ S, f ∈ SB (Matrix (Fin n) (Fin d) k)) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (g : ι → Matrix (Fin n) (Fin n) k), (∀ r, (g r).det = 1) ∧
      ∀ f ∈ S, ∀ M : Matrix (Fin n) (Fin n) k, (∀ i j, M i j ∈ 𝒪[k]) → M.det = 1 → ∀ Y : Matrix (Fin n) (Fin d) k,
        ∑ r, f (g r * (M * Y)) = ∑ r, f (g r * Y) := by
  classical
  have := t2Space k
  let C : Set (Matrix (Fin n) (Fin n) k) := {M | ∀ i j, M i j ∈ 𝒪[k]} ∩ {M | M.det = 1}
  have hC : IsCompact C := by
    refine IsCompact.inter_right ?_ (isClosed_eq (continuous_id.matrix_det) continuous_const)
    have := isCompact_univ_pi fun _ : Fin n => isCompact_univ_pi fun _ : Fin n => isCompact_int k
    exact (show {M : Matrix (Fin n) (Fin n) k | ∀ i j, M i j ∈ 𝒪[k]} =
      Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (𝒪[k] : Set k) from
      Set.ext fun M => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩) ▸ this
  have : CompactSpace C := isCompact_iff_compactSpace.1 hC
  have hmul : ∀ M ∈ C, ∀ N ∈ C, M * N ∈ C := fun M hM N hN =>
    ⟨fun i j => by rw [Matrix.mul_apply]; exact sum_mem fun l _ => mul_mem (hM.1 i l) (hN.1 l j), by
      show (M * N).det = 1
      rw [det_mul, hM.2, hN.2, mul_one]⟩
  have ha1 : ∀ M ∈ C, M * adjugate M = 1 := fun M hM => by rw [mul_adjugate, hM.2, one_smul]
  have ha2 : ∀ M ∈ C, adjugate M * M = 1 := fun M hM => by rw [adjugate_mul, hM.2, one_smul]
  let ρ : C → S → Matrix (Fin n) (Fin d) k → ℂ := fun M f Y => f.1 (M.1 * Y)
  have hρ : IsLocallyConstant ρ := (IsLocallyConstant.iff_eventually_eq _).2 fun M₀ => by
    have : ∀ f : S, ∀ᶠ M in 𝓝 M₀, ∀ v, f.1 (M.1 * (adjugate M₀.1 * v)) = f.1 v := fun f =>
      eventually_comp_eq (fun (M : C) v => M.1 * (adjugate M₀.1 * v)) (fun M v => M₀.1 * (adjugate M.1 * v))
        ((continuous_subtype_val.comp continuous_fst).matrix_mul (continuous_const.matrix_mul continuous_snd))
        (continuous_const.matrix_mul ((continuous_subtype_val.comp continuous_fst).matrix_adjugate.matrix_mul continuous_snd))
        (fun v => by rw [← Matrix.mul_assoc, ha1 _ M₀.2, Matrix.one_mul])
        (fun v => by rw [← Matrix.mul_assoc, ha1 _ M₀.2, Matrix.one_mul])
        (fun M v => by rw [← Matrix.mul_assoc (adjugate M.1), ha2 _ M.2, Matrix.one_mul, ← Matrix.mul_assoc, ha1 _ M₀.2,
          Matrix.one_mul]) (hS _ f.2)
    filter_upwards [eventually_all.2 this] with M hM
    funext f Y
    have := hM f (M₀.1 * Y)
    rwa [← Matrix.mul_assoc (adjugate M₀.1), ha2 _ M₀.2, Matrix.one_mul] at this
  have hfin := hρ.range_finite
  have : Fintype (Set.range ρ) := hfin.fintype
  choose g hg using fun r : Set.range ρ => r.2
  refine ⟨Set.range ρ, inferInstance, ⟨⟨_, ⟨1, fun i j => by rw [one_apply]; split_ifs <;> simp, det_one⟩, rfl⟩⟩,
    fun r => (g r).1, fun r => (g r).2.2, fun f hf M h1 h2 Y => ?_⟩
  have hM : M ∈ C := ⟨h1, h2⟩
  let τ : Set.range ρ → Set.range ρ := fun r => ⟨fun f Y => r.1 f (M * Y), ⟨_, hmul _ (g r).2 _ hM⟩, by
    funext f Y
    rw [← hg r]
    exact congrArg f.1 (Matrix.mul_assoc _ _ _)⟩
  have hτ : Function.Injective τ := fun r r' e => Subtype.ext (funext fun f => funext fun Y => by
    have := congrFun (congrFun (congrArg Subtype.val e) f) (adjugate M * Y)
    simpa only [τ, ← Matrix.mul_assoc, ha1 _ hM, Matrix.one_mul] using this)
  have e : ∀ r (Y : Matrix (Fin n) (Fin d) k), f ((g r).1 * Y) = r.1 ⟨f, hf⟩ Y := fun r Y => congrFun (congrFun (hg r) ⟨f, hf⟩) Y
  simp only [e]
  exact Function.Bijective.sum_comp (Finite.injective_iff_bijective.1 hτ) fun r => r.1 ⟨f, hf⟩ Y

theorem L_char {n : ℕ} (X : Matrix (Fin n) (Fin n) k →* ℂ) (hX : ∀ M : Matrix (Fin n) (Fin n) k, M.det ≠ 0 → X M ≠ 0)
    (M : Matrix (Fin n) (Fin n) k) (hM : M.det = 1) : X M = 1 := by
  have hconj : ∀ A B S : Matrix (Fin n) (Fin n) k, S.det ≠ 0 → S * A = B * S → X A = X B := fun A B S hS h => by
    have := congrArg X h
    rw [map_mul, map_mul, mul_comm] at this
    exact mul_right_cancel₀ (hX S hS) this
  rcases subsingleton_or_nontrivial (Fin n) with hn | hn
  · have : M = 1 := by
      ext i j
      rw [Subsingleton.elim j i, one_apply_eq, ← hM, det_eq_elem_of_subsingleton M i]
    rw [this, map_one]
  refine SpecialLinearGroup.diagonal_transvection_induction' (fun A => X A.1 = 1) ⟨M, hM⟩ ?_ ?_
    fun A B hA hB => by
      show X (A.1 * B.1) = 1
      rw [map_mul, hA, hB, mul_one]
  · intro i j hij c hc
    have h1 := hconj (diagonal (Function.update 1 i c)) (diagonal (Function.update 1 j c)) (Matrix.swap k i j)
      (by
        have := congrArg det (Matrix.swap_mul_self (R := k) i j)
        rw [det_mul, det_one] at this
        exact left_ne_zero_of_mul_eq_one this)
      (by
        ext a b
        simp only [mul_diagonal, diagonal_mul, Matrix.swap, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
          Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
        split_ifs with h
        · subst h
          by_cases ha : a = j
          · subst ha; simp
          · have : Equiv.swap i j a ≠ i := fun e => ha (by rw [Equiv.swap_apply_eq_iff] at e; simpa using e)
            simp [ha, this]
        · simp)
    have h2 : (SpecialLinearGroup.diag2n hij c hc).1 * diagonal (Function.update 1 j c) = diagonal (Function.update 1 i c) := by
      rw [SpecialLinearGroup.diag2n_coe, diagonal_mul_diagonal]
      congr 1
      funext a
      by_cases ha : a = i
      · subst ha; simp [hij]
      · by_cases hb : a = j
        · subst hb; simp [ha, hc]
        · simp [ha, hb]
    have h3 := congrArg X h2
    rw [map_mul, h1] at h3
    exact mul_right_cancel₀ (hX _ (by simp [Finset.prod_update_of_mem, hc])) (h3.trans (one_mul _).symm)
  · intro i j hij a
    have h1 : ∀ c : k, c ≠ 0 → X (transvection i j c) = X (transvection i j 1) := fun c hc =>
      (hconj _ _ (diagonal (Function.update 1 i c)) (by simp [Finset.prod_update_of_mem, hc]) (by
        ext a b
        simp only [mul_diagonal, diagonal_mul, transvection, Matrix.add_apply, one_apply, single_apply]
        by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases hb' : b = j <;> simp_all [eq_comm])).symm
    obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
    have h2 : (1 : k) + ϖ ≠ 0 := fun e => hϖ.inv_notMem (by
      rw [eq_neg_of_add_eq_zero_right e, inv_neg, inv_one]; exact neg_mem (one_mem _))
    have h3 := congrArg X (transvection_mul_transvection_same i j hij (1 : k) ϖ)
    rw [map_mul, h1 _ h2, h1 _ ϖ.ne_zero] at h3
    have h4 : X (transvection i j 1) = 1 :=
      mul_right_cancel₀ (hX _ (by rw [det_transvection_of_ne i j hij]; exact one_ne_zero)) (h3.trans (one_mul _).symm)
    show X (transvection i j a) = 1
    by_cases ha : a = 0
    · rw [ha, transvection_zero, map_one]
    · rw [h1 a ha, h4]

end LocC

section LocD
open Filter Topology GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil hiding SB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open Classical in
theorem L_comb {ϖ : kˣ} (hϖ : IsUnif ϖ) (d n : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℂ) (γ : ι → Matrix (Fin n) (Fin n) k) (j : ι → ℕ),
      (∀ i, (γ i).det = ((ϖ : k)⁻¹) ^ j i) ∧
      (∀ (Λ : Submodule 𝒪[k] (Fin d → k)) (Y : Matrix (Fin n) (Fin d) k),
        ∑ i, m i * (if γ i * Y ∈ matLat _ Λ then 1 else 0) = if IsPrimFrame Λ Y then 1 else 0) ∧
      ∀ x : ℂ, ∑ i, m i * x ^ j i = ∏ i ∈ Finset.range n, (1 - (resCard k : ℂ) ^ i * x) := by
  induction n with
  | zero =>
    refine ⟨PUnit, inferInstance, 1, 1, 0, by simp, fun Λ Y => ?_, by simp⟩
    simp [isPrimFrame_iff, mem_matLat]
  | succ n ih =>
    obtain ⟨ι, _, m, γ, j, h1, h2, h3⟩ := ih
    have : Fintype 𝓀[k] := Fintype.ofFinite _
    choose l hl using IsLocalRing.residue_surjective (R := 𝒪[k])
    refine ⟨ι ⊕ ι × (Fin n → 𝓀[k]), inferInstance, Sum.elim m fun p => -m p.1,
      Sum.elim (fun i => consBlock 1 0 (γ i))
        fun p => consBlock (ϖ : k)⁻¹ ((ϖ : k)⁻¹ • fun i => (l (p.2 i) : k)) (γ p.1),
      Sum.elim j fun p => j p.1 + 1, ?_, fun Λ Y => ?_, fun x => ?_⟩
    · rintro (i | p) <;> simp [det_consBlock, h1, pow_succ']
    · rw [indicator_isPrimFrame_succ hϖ l hl, ← h2, Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp only [Sum.elim_inl, Sum.elim_inr, consBlock_mul_mem, smul_vecMul, ← smul_add, one_smul, zero_vecMul,
        add_zero, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : γ i * Y.submatrix Fin.succ id ∈ matLat _ Λ
      · simp only [h, true_and, if_true, mul_one, mul_sub, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
        ring
      · simp [h]
    · rw [Finset.prod_range_succ, ← h3, Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        resCard, Nat.card_eq_fintype_card, Finset.sum_mul, ← Finset.sum_add_distrib, nsmul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring

theorem L_orth (ψ : AddChar k ℂ) (hc : Continuous ψ) (h1 : ψ ≠ 1) {n d : ℕ}
    (B : SB (Matrix (Fin n) (Fin d) k) →ₗ[ℂ] SB (Matrix (Fin n) (Fin d) k) →ₗ⋆[ℂ] ℂ)
    (hmod : ∀ (Z : Matrix (Fin n) (Fin d) k) (f f' g g' : SB (Matrix (Fin n) (Fin d) k)),
      (∀ Y, f'.1 Y = ψ (trace (Y * Zᵀ)) * f.1 Y) → (∀ Y, g'.1 Y = ψ (trace (Y * Zᵀ)) * g.1 Y) → B f' g' = B f g)
    (hψ : ∀ x, ‖ψ x‖ = 1) (f g : SB (Matrix (Fin n) (Fin d) k)) (h : ∀ Y, f.1 Y = 0 ∨ g.1 Y = 0) : B f g = 0 := by
  classical
  let A : Subalgebra ℂ (Matrix (Fin n) (Fin d) k → ℂ) :=
    { carrier := {a | IsLocallyConstant a ∧ ∀ f f' g g' : SB (Matrix (Fin n) (Fin d) k),
        f'.1 = a * f.1 → g'.1 = star a * g.1 → B f' g = B f g'}
      mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, fun f f' g g' e e' => by
        rw [ha.2 ⟨_, L_mul_mem hb.1 f.2⟩ f' g ⟨_, L_mul_mem (ha.1.comp star) g.2⟩ (by rw [e, mul_assoc]) rfl]
        exact hb.2 _ _ _ _ rfl (by rw [e', star_mul, mul_assoc]; rfl)⟩
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun f f' g g' e e' => by
        rw [show f' = ⟨_, L_mul_mem ha.1 f.2⟩ + ⟨_, L_mul_mem hb.1 f.2⟩ from Subtype.ext (by rw [e, add_mul]; rfl),
          show g' = ⟨_, L_mul_mem (ha.1.comp star) g.2⟩ + ⟨_, L_mul_mem (hb.1.comp star) g.2⟩ from
            Subtype.ext (by rw [e', star_add, add_mul]; rfl), map_add, map_add, LinearMap.add_apply,
          ha.2 f _ g ⟨_, L_mul_mem (ha.1.comp star) g.2⟩ rfl rfl, hb.2 f _ g ⟨_, L_mul_mem (hb.1.comp star) g.2⟩ rfl rfl]⟩
      algebraMap_mem' := fun r => ⟨IsLocallyConstant.const r, fun f f' g g' e e' => by
        rw [show f' = r • f from Subtype.ext e, show g' = star r • g from Subtype.ext e', map_smul, map_smulₛₗ]
        simp⟩ }
  have hch : ∀ Z : Matrix (Fin n) (Fin d) k, IsLocallyConstant fun Y : Matrix (Fin n) (Fin d) k => ψ (trace (Y * Zᵀ)) :=
    fun Z => (L_lc hc).comp_continuous (continuous_id.matrix_mul continuous_const).matrix_trace
  have hU : IsClopen (Function.support f.1) := (f.2.1.isClopen_fiber 0).compl
  obtain ⟨a, ha, e⟩ := L_interp A (fun a ha => ha.1) (fun x y hxy => by
    obtain ⟨z, hz⟩ := L_nondeg h1 (x := flat (Equiv.refl (Fin n × Fin d)) (x - y))
      (fun e => hxy (sub_eq_zero.1 ((LinearEquiv.map_eq_zero_iff _).1 e)))
    obtain ⟨Z, rfl⟩ := (flat (R := k) (Equiv.refl (Fin n × Fin d))).surjective z
    rw [flat_dot] at hz
    refine ⟨fun Y => ψ (trace (Y * Zᵀ)), ⟨hch Z, fun f f' g g' e e' => ?_⟩, fun e => hz ?_⟩
    · refine hmod Z f f' g' g (congrFun e) fun Y => ?_
      rw [e', Pi.mul_apply, Pi.star_apply, ← mul_assoc, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ]
      simp
    · have e' : ψ (trace (x * Zᵀ)) = ψ (trace (y * Zᵀ)) := e
      rw [Matrix.sub_mul, trace_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, e', ← AddChar.map_add_eq_mul, add_neg_cancel,
        AddChar.map_zero_eq_one]) (IsCompact.union f.2.2 g.2.2)
    (f := (Function.support f.1).indicator 1) (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hU).isLocallyConstant
  rw [ha.2 f f g 0 (funext fun Y => ?_) (funext fun Y => ?_), map_zero]
  · by_cases hY : f.1 Y = 0
    · simp [hY]
    · rw [Pi.mul_apply, e Y (.inl (subset_tsupport _ hY)), Set.indicator_of_mem (Function.mem_support.2 hY)]; simp
  · by_cases hY : g.1 Y = 0
    · simp [hY]
    · rw [Pi.mul_apply, Pi.star_apply, e Y (.inr (subset_tsupport _ hY)),
        Set.indicator_of_notMem (by simpa using (h Y).resolve_right hY)]
      simp

theorem L_norm {ϖ : kˣ} (hϖ : IsUnif ϖ) {n d : ℕ} (i₀ : Fin n) (x : ℂ)
    (B : SB (Matrix (Fin n) (Fin d) k) →ₗ[ℂ] SB (Matrix (Fin n) (Fin d) k) →ₗ⋆[ℂ] ℂ)
    (htr : ∀ (Y₀ : Matrix (Fin n) (Fin d) k) (f f' g g' : SB (Matrix (Fin n) (Fin d) k)),
      (∀ Y, f'.1 Y = f.1 (Y + Y₀)) → (∀ Y, g'.1 Y = g.1 (Y + Y₀)) → B f' g' = B f g)
    (horth : ∀ f g : SB (Matrix (Fin n) (Fin d) k), (∀ Y, f.1 Y = 0 ∨ g.1 Y = 0) → B f g = 0)
    (hpos : ∀ f, f ≠ 0 → B f f ≠ 0)
    (hun : ∀ f f' : SB (Matrix (Fin n) (Fin d) k),
      (∀ Y, f'.1 Y = x * f.1 ((diagonal (Function.update 1 i₀ (ϖ : k)) : Matrix (Fin n) (Fin n) k) * Y)) → B f' f' = B f f) :
    ‖x‖ ^ 2 * (resCard k : ℝ) ^ d = 1 := by
  classical
  have := t2Space k
  have : Fintype 𝓀[k] := Fintype.ofFinite _
  choose l hl using IsLocalRing.residue_surjective (R := 𝒪[k])
  let K : Set (Matrix (Fin n) (Fin d) k) := {M | ∀ i j, M i j ∈ 𝒪[k]}
  have eK : K = Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin d => (𝒪[k] : Set k) :=
    Set.ext fun M => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  have hKc : IsCompact K := eK ▸ isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_int k
  have hK : IsClopen K := ⟨hKc.isClosed, eK ▸ isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_int k⟩
  let f : SB (Matrix (Fin n) (Fin d) k) := ⟨K.indicator 1,
    (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hK).isLocallyConstant,
    HasCompactSupport.intro hKc fun x hx => Set.indicator_of_notMem hx _⟩
  have hf0 : f ≠ 0 := fun e => by
    have := congrFun (congrArg Subtype.val e) 0
    rw [show f.1 0 = 1 from Set.indicator_of_mem (show (0 : Matrix (Fin n) (Fin d) k) ∈ K from fun _ _ => zero_mem _) _]
      at this
    exact one_ne_zero this
  let Yt : (Fin d → 𝓀[k]) → Matrix (Fin n) (Fin d) k := fun t => Matrix.of fun i j =>
    if i = i₀ then (ϖ : k)⁻¹ * l (t j) else 0
  let ft : (Fin d → 𝓀[k]) → SB (Matrix (Fin n) (Fin d) k) := fun t => ⟨fun Y => f.1 (Y + Yt t),
    f.2.1.comp_continuous (continuous_add_const _), f.2.2.comp_homeomorph (Homeomorph.addRight (Yt t))⟩
  have ha : ∀ t Y, Y + Yt t ∈ K → (diagonal (Function.update 1 i₀ (ϖ : k)) : Matrix (Fin n) (Fin n) k) * Y ∈ K :=
    fun t Y h i j => by
      have := h i j
      rw [diagonal_mul]
      by_cases hi : i = i₀
      · subst hi
        have h2 := sub_mem (mul_mem hϖ.mem this) (l (t j)).2
        simpa [Yt, mul_add] using h2
      · simpa [Yt, hi] using this
  have hb : ∀ Y, (diagonal (Function.update 1 i₀ (ϖ : k)) : Matrix (Fin n) (Fin n) k) * Y ∈ K → ∃ t, Y + Yt t ∈ K :=
    fun Y h => by
      have h0 : ∀ j, -((ϖ : k) * Y i₀ j) ∈ 𝒪[k] := fun j => neg_mem (by simpa [diagonal_mul] using h i₀ j)
      refine ⟨fun j => IsLocalRing.residue _ ⟨_, h0 j⟩, fun i j => ?_⟩
      by_cases hi : i = i₀
      · subst hi
        have h2 := (hϖ.residue_eq_iff _ _).1 (hl (IsLocalRing.residue _ ⟨_, h0 j⟩))
        simpa [Yt, mul_add, add_comm] using h2
      · simpa [Yt, hi, diagonal_mul] using h i j
  have hc : ∀ t s Y, Y + Yt t ∈ K → Y + Yt s ∈ K → t = s := fun t s Y h h' => funext fun j => by
    rw [← hl (t j), ← hl (s j), hϖ.residue_eq_iff]
    simpa [Yt, mul_sub] using sub_mem (h i₀ j) (h' i₀ j)
  have h1 := hun f (x • ∑ t, ft t) fun Y => by
    simp only [Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ft, f]
    congr 1
    by_cases h : (diagonal (Function.update 1 i₀ (ϖ : k)) : Matrix (Fin n) (Fin n) k) * Y ∈ K
    · obtain ⟨t, ht⟩ := hb Y h
      rw [Finset.sum_eq_single t (fun s _ hs => Set.indicator_of_notMem (fun h' => hs (hc s t Y h' ht)) _) (by simp),
        Set.indicator_of_mem ht, Set.indicator_of_mem h]
      rfl
    · rw [Finset.sum_eq_zero fun s _ => Set.indicator_of_notMem (fun h' => h (ha s Y h')) _, Set.indicator_of_notMem h]
  have h2 : B (∑ t, ft t) (∑ t, ft t) = (resCard k : ℂ) ^ d * B f f := by
    rw [map_sum, Finset.sum_congr rfl fun s _ => show B (∑ t, ft t) (ft s) = B f f by
      rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single s (fun t _ ht => horth _ _ fun Y => ?_) (by simp)]
      · exact htr (Yt s) f _ f _ (fun _ => rfl) fun _ => rfl
      · by_contra hh
        push Not at hh
        exact ht (hc t s Y (Set.mem_of_indicator_ne_zero hh.1) (Set.mem_of_indicator_ne_zero hh.2))]
    simp [resCard]
  rw [map_smulₛₗ, map_smul, LinearMap.smul_apply, h2, smul_eq_mul, smul_eq_mul] at h1
  have h3 : ((‖x‖ ^ 2 * (resCard k : ℝ) ^ d : ℝ) : ℂ) * B f f = 1 * B f f := by
    rw [one_mul]
    refine Eq.trans ?_ h1
    rw [← Complex.normSq_eq_norm_sq, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    push_cast
    ring
  exact_mod_cast mul_right_cancel₀ (hpos f hf0) h3

end LocD

open GlobalTheory.SplitFlip in
theorem comb {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k ℂ) (hc : Continuous ψ) (h1 : ψ ≠ 1) {n d : ℕ} (hnd : 2 * n < d + 2)
    (χ : GL (Fin n) k →* ℂ)
    (B : SB (Matrix (Fin n) (Fin d) k) →ₗ[ℂ] SB (Matrix (Fin n) (Fin d) k) →ₗ⋆[ℂ] ℂ)
    (htr : ∀ (Y₀ : Matrix (Fin n) (Fin d) k) (f f' g g' : SB (Matrix (Fin n) (Fin d) k)),
      (∀ Y, f'.1 Y = f.1 (Y + Y₀)) → (∀ Y, g'.1 Y = g.1 (Y + Y₀)) → B f' g' = B f g)
    (hmod : ∀ (Z : Matrix (Fin n) (Fin d) k) (f f' g g' : SB (Matrix (Fin n) (Fin d) k)),
      (∀ Y, f'.1 Y = ψ (trace (Y * Zᵀ)) * f.1 Y) → (∀ Y, g'.1 Y = ψ (trace (Y * Zᵀ)) * g.1 Y) → B f' g' = B f g)
    (hψ : ∀ x, ‖ψ x‖ = 1)
    (hpos : ∀ f, f ≠ 0 → B f f ≠ 0)
    (hun : ∀ (γ : GL (Fin n) k) (f f' : SB (Matrix (Fin n) (Fin d) k)),
      (∀ Y, f'.1 Y = χ γ * f.1 (γ.1 * Y)) → B f' f' = B f f)
    (S : Finset (Matrix (Fin n) (Fin d) k → ℂ)) (hS : ∀ f ∈ S, f ∈ SB (Matrix (Fin n) (Fin d) k)) :
    ∃ z : GL (Fin n) k →₀ ℂ, (z.sum fun _ a => a) ≠ 0 ∧
      ∀ f ∈ S, ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≠ n → (z.sum fun γ a => a * (χ γ * f (γ.1 * Y))) = 0 := by
  classical
  let X : Matrix (Fin n) (Fin n) k →* ℂ :=
    { toFun := fun M => if h : M.det ≠ 0 then χ (GeneralLinearGroup.mkOfDetNeZero M h) else 0
      map_one' := by
        rw [dif_pos (by simp), ← map_one χ]
        congr 1
        exact Units.ext rfl
      map_mul' := fun M N => by
        by_cases hM : M.det ≠ 0
        · by_cases hN : N.det ≠ 0
          · rw [dif_pos hM, dif_pos hN, dif_pos (by rw [det_mul]; exact mul_ne_zero hM hN), ← map_mul]
            congr 1
            exact Units.ext rfl
          · rw [dif_neg hN, mul_zero, dif_neg (by simp [not_not.1 hN])]
        · rw [dif_neg hM, zero_mul, dif_neg (by simp [not_not.1 hM])] }
  have hXe : ∀ M (h : M.det ≠ 0), χ (GeneralLinearGroup.mkOfDetNeZero M h) = X M := fun M h => by
    show _ = dite _ _ _
    rw [dif_pos h]
  have hX : ∀ M : Matrix (Fin n) (Fin n) k, M.det ≠ 0 → X M ≠ 0 := fun M h => by
    rw [← hXe M h]; exact ((Group.isUnit _).map χ).ne_zero
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
  obtain ⟨ι, _, m, γ, j, g1, g2, g3⟩ := L_comb hϖ d n
  obtain ⟨ρ, _, _, g, r1, r2⟩ := L_avg S hS
  obtain ⟨x, hx, hx'⟩ : ∃ x : ℂ, (∀ i, x ^ j i * X (γ i) = 1) ∧
      ∀ i < n, 1 - (GlobalTheory.SplitWeil.resCard k : ℂ) ^ i * x ≠ 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, fun i => by rw [Subsingleton.elim (γ i) 1, map_one, one_pow, mul_one], fun i hi => by omega⟩
    let i₀ : Fin n := ⟨0, hn⟩
    have hd : (diagonal (Function.update 1 i₀ (ϖ : k)) : Matrix (Fin n) (Fin n) k).det = ϖ := by
      simp [Finset.prod_update_of_mem]
    refine ⟨X (diagonal (Function.update 1 i₀ (ϖ : k))), fun i => ?_, fun i hi h0 => ?_⟩
    · rw [← map_pow, ← map_mul]
      exact L_char X hX _ (by rw [det_mul, det_pow, hd, g1, ← mul_pow, mul_inv_cancel₀ ϖ.ne_zero, one_pow])
    · have h2 := L_norm hϖ i₀ _ B htr (L_orth ψ hc h1 B hmod hψ) hpos fun f f' e =>
        hun (GeneralLinearGroup.mkOfDetNeZero _ (hd ▸ ϖ.ne_zero)) f f' fun Y => by rw [hXe]; exact e Y
      have h3 := congrArg (fun z => ‖z‖ ^ 2) (sub_eq_zero.1 h0)
      simp only [norm_one, one_pow, norm_mul, norm_pow, Complex.norm_natCast, mul_pow] at h3
      have hq : (1 : ℝ) < GlobalTheory.SplitWeil.resCard k := by exact_mod_cast (Finite.one_lt_card : 1 < GlobalTheory.SplitWeil.resCard k)
      have h4 : (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = (GlobalTheory.SplitWeil.resCard k : ℝ) ^ (i * 2) := by
        rw [pow_mul]
        linear_combination (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d * h3 + ((GlobalTheory.SplitWeil.resCard k : ℝ) ^ i) ^ 2 * h2
      have := pow_right_injective₀ (by linarith) hq.ne' h4
      omega
  have hdet : ∀ p : ι × ρ, (g p.2 * γ p.1).det ≠ 0 := fun p => by
    rw [det_mul, r1, one_mul, g1]; exact pow_ne_zero _ (inv_ne_zero ϖ.ne_zero)
  have hsum : ∀ G : GL (Fin n) k → ℂ, ((∑ p : ι × ρ, Finsupp.single (GeneralLinearGroup.mkOfDetNeZero _ (hdet p))
      (m p.1 * x ^ j p.1)).sum fun γ a => a * G γ) =
      ∑ p : ι × ρ, m p.1 * x ^ j p.1 * G (GeneralLinearGroup.mkOfDetNeZero _ (hdet p)) := fun G => by
    rw [← Finsupp.sum_finset_sum_index (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _]
    exact Finset.sum_congr rfl fun p _ => Finsupp.sum_single_index (zero_mul _)
  refine ⟨∑ p : ι × ρ, Finsupp.single (GeneralLinearGroup.mkOfDetNeZero _ (hdet p)) (m p.1 * x ^ j p.1), ?_,
    fun f hf Y hY => ?_⟩
  · have := hsum fun _ => 1
    simp only [mul_one] at this
    rw [this, Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, g3]
    exact mul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
      (Finset.prod_ne_zero_iff.2 fun i hi => hx' i (Finset.mem_range.1 hi))
  · rw [hsum, Fintype.sum_prod_type, ← L_mobius (fun i => Submodule.span 𝒪[k] (Set.range (γ i * Y).row)) m
      (fun i => ∑ r, f (g r * (γ i * Y))) (fun Λ => ?_) fun i i' e => ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hXe, map_mul, L_char X hX _ (r1 r), one_mul, ← Matrix.mul_assoc]
      show m i * x ^ j i * (X (γ i) * f (g r * γ i * Y)) = _
      linear_combination m i * f (g r * γ i * Y) * hx i
    · have := g2 Λ Y
      rw [if_neg fun h => hY (h.1.trans (Fintype.card_fin n))] at this
      refine Eq.trans ?_ this
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      refine if_congr ?_ rfl rfl
      rw [Submodule.span_le, Set.range_subset_iff]
      rfl
    · obtain ⟨M, m1, m2, m3⟩ := L_move (Y := γ i * Y) (by
        rwa [rank_mul_eq_right_of_isUnit_det _ _ (by
          rw [g1]; exact (pow_ne_zero _ (inv_ne_zero ϖ.ne_zero)).isUnit)]) e
      rw [← m3, r2 f hf M m1 m2]

end PositivityTheory.Member.ZakTransform
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace PositivityTheory.Member.ZakTransform

namespace S
section Real
open Complex
open scoped Real ContDiff

theorem hadamard_lemma : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ f → f 0 = 0 → ∃ g : Fin n → (Fin n → ℝ) → ℂ, (∀ i, ContDiff ℝ ∞ (g i)) ∧ ∀ x, f x = ∑ i, (x i : ℂ) * g i x := by
  intro n f hf h0
  have hD : ∀ v : Fin n → ℝ, ContDiff ℝ ∞ (fun w => fderiv ℝ f w v) := fun v =>
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hmean : ∀ h : (Fin n → ℝ) → ℂ, ContDiff ℝ ∞ h →
      ContDiff ℝ ∞ (fun x : Fin n → ℝ => ∫ s in (0 : ℝ)..1, h (s • x)) := by
    intro h hh
    let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
    have hk : IsCompact (Metric.closedBall (0 : ℝ) 2) := isCompact_closedBall _ _
    have hloc : MeasureTheory.LocallyIntegrable
        ((Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) MeasureTheory.volume :=
      (MeasureTheory.locallyIntegrable_const (1 : ℝ)).indicator measurableSet_Ioc
    have hsm : ContDiffOn ℝ ∞ (Function.uncurry fun (p : Fin n → ℝ) (t : ℝ) => b t • h ((-t) • p))
        (Set.univ ×ˢ Set.univ) := by
      refine ContDiff.contDiffOn ?_
      exact (b.contDiff.comp contDiff_snd).smul (hh.comp (contDiff_snd.neg.smul contDiff_fst))
    have key := MeasureTheory.contDiffOn_convolution_right_with_param_comp (n := (⊤ : ℕ∞))
      (μ := MeasureTheory.volume) (ContinuousLinearMap.lsmul ℝ ℝ) (s := Set.univ)
      (v := fun _ : Fin n → ℝ => (0 : ℝ)) contDiffOn_const
      (g := fun (p : Fin n → ℝ) (t : ℝ) => b t • h ((-t) • p)) isOpen_univ hk
      (fun p t _ ht => by
        have : b t = 0 := image_eq_zero_of_notMem_tsupport (by rw [b.tsupport_eq]; exact ht)
        simp [this]) hloc hsm
    rw [contDiffOn_univ] at key
    convert key using 2 with x
    rw [MeasureTheory.convolution_def, intervalIntegral.integral_of_le zero_le_one,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    congr 1
    funext t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
    · have : b (-t) = 1 := b.one_of_mem_closedBall (by
        rw [mem_closedBall_zero_iff, norm_neg, Real.norm_eq_abs, abs_of_pos ht.1]; exact ht.2)
      simp [ht, this]
    · simp [ht]
  refine ⟨fun i x => ∫ s in (0 : ℝ)..1, fderiv ℝ f (s • x) (Pi.single i 1),
    fun i => hmean _ (hD _), fun x => ?_⟩
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => f (s • x)) (fderiv ℝ f (s • x) x) s := by
    intro s _
    have := (hd (s • x)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const x)
    rw [one_smul] at this
    exact this
  have hcv : ∀ v : Fin n → ℝ, Continuous (fun s : ℝ => fderiv ℝ f (s • x) v) := fun v =>
    (hD v).continuous.comp (continuous_id.smul continuous_const)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((hcv x).intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, h0, sub_zero] at hftc
  rw [← hftc]
  have hx : ∀ s : ℝ, fderiv ℝ f (s • x) x =
      ∑ i, (x i : ℂ) * fderiv ℝ f (s • x) (Pi.single i 1) := by
    intro s
    calc fderiv ℝ f (s • x) x = fderiv ℝ f (s • x) (∑ i, x i • (Pi.single i 1 : Fin n → ℝ)) :=
          congrArg (fderiv ℝ f (s • x)) (pi_eq_sum_univ' x)
      _ = _ := by simp only [map_sum, map_smul, Complex.real_smul]
  simp_rw [hx]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul]
  · exact fun i _ => (continuous_const.mul (hcv _)).intervalIntegrable 0 1

theorem dense_hasCompactSupport : ∀ (n : ℕ), Dense {f : SchwartzMap (Fin n → ℝ) ℂ | HasCompactSupport (f : (Fin n → ℝ) → ℂ)} := by
  intro n f
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  set u : (Fin n → ℝ) → ℝ := (b : (Fin n → ℝ) → ℝ) - fun _ => 1 with hu
  have hus : ContDiff ℝ ∞ u := b.contDiff.sub contDiff_const
  have hub : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ i u x‖ ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := (b.hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) i).exists_bound_of_continuous
      ((b.contDiff (n := ⊤)).continuous_iteratedFDeriv (by exact_mod_cast le_top))
    refine ⟨C + 1, by linarith [(norm_nonneg _).trans (hC 0)], fun x => ?_⟩
    rw [hu, iteratedFDeriv_sub b.contDiff contDiff_const]
    refine (norm_sub_le _ _).trans (add_le_add (hC x) ?_)
    by_cases hi : i = 0
    · subst hi; simp
    · rw [iteratedFDeriv_const_of_ne hi]; simp
  choose C hC0 hC using hub
  let L : ℕ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := fun R =>
    ((R : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ _
  have hL : ∀ R x, ‖L R x‖ = ‖x‖ / ((R : ℝ) + 1) := by
    intro R x
    show ‖((R : ℝ) + 1)⁻¹ • x‖ = _
    rw [norm_smul, Real.norm_of_nonneg (by positivity), div_eq_inv_mul]
  have hL1 : ∀ R, ‖L R‖ ≤ 1 := fun R =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [hL, one_mul]
      exact div_le_self (norm_nonneg _) (by linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)])
  have hsm : ∀ R, ContDiff ℝ ∞ (fun x => b (L R x) • f x) := fun R =>
    (b.contDiff.comp (L R).contDiff).smul (f.smooth ⊤)
  have hcs : ∀ R, HasCompactSupport (fun x => b (L R x) • f x) := by
    intro R
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℝ) (2 * ((R : ℝ) + 1))) ?_
    intro x hx
    rw [mem_closedBall_zero_iff, not_le] at hx
    rw [b.zero_of_le_dist, zero_smul]
    rw [dist_zero_right, hL, le_div_iff₀ (by positivity)]
    exact hx.le
  refine mem_closure_of_tendsto (b := Filter.atTop) (f := fun R : ℕ => (hcs R).toSchwartzMap (hsm R))
    ?_ (Filter.Eventually.of_forall hcs)
  rw [(schwartz_withSeminorms ℂ (Fin n → ℝ) ℂ).tendsto_nhds]
  rintro ⟨k, j⟩ ε hε
  set M : ℝ := ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * C i * SchwartzMap.seminorm ℂ (k + 1) (j - i) f with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC0 i)) (apply_nonneg _ _)
  have hlim : Filter.Tendsto (fun R : ℕ => M * (1 / ((R : ℝ) + 1))) Filter.atTop (nhds (M * 0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul M
  rw [mul_zero] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with R hR
  refine lt_of_le_of_lt ?_ hR
  rw [SchwartzMap.schwartzSeminormFamily_apply]
  refine SchwartzMap.seminorm_le_bound ℂ k j _ (by positivity) fun x => ?_
  have e : (⇑((hcs R).toSchwartzMap (hsm R) - f) : (Fin n → ℝ) → ℂ) =
      fun x => (u ∘ L R) x • f x := by
    funext y
    show b (L R y) • f y - f y = (b (L R y) - 1) • f y
    rw [sub_smul, one_smul]
  rw [e]
  have hR0 : (0 : ℝ) < R + 1 := by positivity
  by_cases hx : ‖x‖ < R + 1
  · have hz : (fun x => (u ∘ L R) x • f x) =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
      have : b (L R y) = 1 := b.one_of_mem_closedBall (by
        rw [mem_closedBall_zero_iff, hL]
        exact (div_le_one hR0).2 (le_of_lt hy))
      show (b (L R y) - 1) • f y = 0
      rw [this, sub_self, zero_smul]
    rw [(hz.iteratedFDeriv ℝ j).self_of_nhds, iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero, mul_zero]
    positivity
  · rw [not_lt] at hx
    have h1 := norm_iteratedFDeriv_smul_le (hus.comp (L R).contDiff) (f.smooth ⊤) x (n := j)
      (by exact_mod_cast le_top)
    rw [mul_one_div, le_div_iff₀ hR0]
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ j (fun x => (u ∘ L R) x • f x) x‖ * ((R : ℝ) + 1)
        ≤ ‖x‖ ^ k * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (u ∘ L R) x‖ * ‖iteratedFDeriv ℝ (j - i) f x‖) * ‖x‖ := by
          gcongr
      _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (u ∘ L R) x‖ *
          (‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (j - i) f x‖) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ M := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h2 : ‖iteratedFDeriv ℝ i (u ∘ L R) x‖ ≤ C i := by
            rw [(L R).iteratedFDeriv_comp_right hus x (by exact_mod_cast le_top)]
            refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
            refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans (hC i _)
            exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL1 R)
          have h3 := SchwartzMap.le_seminorm ℂ (k + 1) (j - i) f x
          have h4 := hC0 i
          gcongr

theorem exists_quot : ∃ q : ℝ → ℂ, ContDiffOn ℝ ∞ q (Metric.ball 0 1) ∧
    ∀ t ∈ Metric.ball (0 : ℝ) 1, (t : ℂ) = (cexp (2 * π * I * t) - 1) * q t := by
  set E : ℂ → ℂ := fun z => cexp (2 * π * I * z) with hE
  have hEd : Differentiable ℂ E := by rw [hE]; fun_prop
  have hd : Differentiable ℂ (dslope E 0) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).2 hEd.differentiableOn
  have hc : ContDiff ℝ ∞ (fun t : ℝ => dslope E 0 (t : ℂ)) :=
    (hd.contDiff.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff
  have hmul : ∀ t : ℝ, (t : ℂ) * dslope E 0 t = cexp (2 * π * I * t) - 1 := by
    intro t
    have := sub_smul_dslope E 0 (t : ℂ)
    simpa [hE] using this
  have hne : ∀ t ∈ Metric.ball (0 : ℝ) 1, dslope E 0 (t : ℂ) ≠ 0 := by
    intro t ht h0
    by_cases h : t = 0
    · subst h
      have hD : HasDerivAt E (cexp (2 * π * I * 0) * (2 * π * I * 1)) 0 :=
        ((hasDerivAt_id (0 : ℂ)).const_mul (2 * π * I)).cexp
      rw [Complex.ofReal_zero, dslope_same, hD.deriv] at h0
      simp [Real.pi_ne_zero] at h0
    · have h1 := hmul t
      rw [h0, mul_zero, eq_comm, sub_eq_zero, Complex.exp_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      have h2 : (t : ℂ) = k := by
        have h3 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
        apply mul_left_cancel₀ h3
        rw [hk]; ring
      have h4 : t = k := by exact_mod_cast h2
      rw [mem_ball_zero_iff, Real.norm_eq_abs, h4] at ht
      have h5 : |k| < 1 := by exact_mod_cast ht
      have h6 : k = 0 := Int.abs_lt_one_iff.1 h5
      exact h (by rw [h4, h6]; simp)
  refine ⟨fun t => (dslope E 0 (t : ℂ))⁻¹, hc.contDiffOn.inv hne, fun t ht => ?_⟩
  rw [← hmul t, mul_assoc, mul_inv_cancel₀ (hne t ht), mul_one]

theorem exists_div (n : ℕ) (f : SchwartzMap (Fin n → ℝ) ℂ)
    (hf : tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1) (h0 : f 0 = 0) :
    ∃ g : Fin n → SchwartzMap (Fin n → ℝ) ℂ, (∀ i, HasCompactSupport (g i : (Fin n → ℝ) → ℂ)) ∧
      ∀ x, f x = ∑ i, (cexp (2 * π * I * x i) - 1) * g i x := by
  obtain ⟨q, hq, hq'⟩ := exists_quot
  obtain ⟨h, hh, hh'⟩ := hadamard_lemma n f (f.smooth ⊤) h0
  have hK : IsCompact (tsupport (f : (Fin n → ℝ) → ℂ)) :=
    (isCompact_closedBall (0 : Fin n → ℝ) 1).of_isClosed_subset (isClosed_tsupport _)
      (hf.trans Metric.ball_subset_closedBall)
  obtain ⟨r, hr, hr'⟩ := exists_lt_subset_ball (isClosed_tsupport _) hf
  set r' : ℝ := max r (1 / 2) with hr'def
  have hr1 : r' < 1 := max_lt hr (by norm_num)
  have hr0 : 0 < r' := lt_max_of_lt_right (by norm_num)
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨r', (r' + 1) / 2, hr0, by linarith⟩
  have hbs : tsupport (b : (Fin n → ℝ) → ℝ) ⊆ Metric.ball 0 1 := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by show (r' + 1) / 2 < 1; linarith)
  have hcoord : ∀ (i : Fin n), ∀ x ∈ Metric.ball (0 : Fin n → ℝ) 1, x i ∈ Metric.ball (0 : ℝ) 1 := by
    intro i x hx
    rw [mem_ball_zero_iff] at hx ⊢
    exact (norm_le_pi_norm x i).trans_lt hx
  have hsm : ∀ i, ContDiff ℝ ∞ (fun x : Fin n → ℝ => b x • (q (x i) * h i x)) := by
    intro i
    rw [← contMDiff_iff_contDiff]
    refine contMDiff_of_tsupport fun x hx => ?_
    rw [contMDiffAt_iff_contDiffAt]
    have hx' : x ∈ Metric.ball (0 : Fin n → ℝ) 1 := hbs (tsupport_smul_subset_left _ _ hx)
    refine b.contDiff.contDiffAt.smul (ContDiffAt.mul ?_ (hh i).contDiffAt)
    exact ContDiffAt.comp x (g := q) (f := fun x : Fin n → ℝ => x i)
      (hq.contDiffAt (Metric.isOpen_ball.mem_nhds (hcoord i x hx'))) (contDiffAt_apply ℝ ℝ i x)
  have hcs : ∀ i, HasCompactSupport (fun x : Fin n → ℝ => b x • (q (x i) * h i x)) :=
    fun i => b.hasCompactSupport.smul_right
  refine ⟨fun i => (hcs i).toSchwartzMap (hsm i), hcs, fun x => ?_⟩
  show f x = ∑ i, (cexp (2 * π * I * x i) - 1) * (b x • (q (x i) * h i x))
  have hb : f x = b x • f x := by
    by_cases hx : x ∈ tsupport (f : (Fin n → ℝ) → ℂ)
    · rw [b.one_of_mem_closedBall, one_smul]
      exact Metric.ball_subset_closedBall (Metric.ball_subset_ball (le_max_left _ _) (hr' hx))
    · rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]
  by_cases hx : x ∈ Metric.ball (0 : Fin n → ℝ) 1
  · rw [hb, hh' x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, ← mul_assoc, ← hq' _ (hcoord i x hx)]
  · have : b x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hbs h)
    rw [hb, this]; simp

theorem zero_of_ball (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (hχ : ∀ (i : Fin n) (f g : SchwartzMap (Fin n → ℝ) ℂ), (∀ x, g x = cexp (2 * π * I * x i) * f x) → T g = T f)
    (f : SchwartzMap (Fin n → ℝ) ℂ) (hf : tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1) (h0 : f 0 = 0) : T f = 0 := by
    obtain ⟨g, hg, hg'⟩ := exists_div n f hf h0
    have hsm : ∀ i, ContDiff ℝ ∞ (fun x : Fin n → ℝ => cexp (2 * π * I * x i) * g i x) := by
      intro i
      refine ContDiff.mul ?_ ((g i).smooth ⊤)
      exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i))).cexp
    have hcs : ∀ i, HasCompactSupport (fun x : Fin n → ℝ => cexp (2 * π * I * x i) * g i x) :=
      fun i => (hg i).mul_left
    have e : f = ∑ i, ((hcs i).toSchwartzMap (hsm i) - g i) := by
      ext x
      rw [hg' x, _root_.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = cexp (2 * π * I * x i) * g i x - g i x
      ring
    rw [e, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_sub, hχ i (g i) _ (fun x => rfl), sub_self]

theorem eq_delta (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (hχ : ∀ (t : ℝ) (i : Fin n) (f g : SchwartzMap (Fin n → ℝ) ℂ),
      (∀ x, g x = cexp (2 * π * I * (t * x i : ℝ)) * f x) → T g = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, T f = a * f 0 := by
  have hA : ∀ f : SchwartzMap (Fin n → ℝ) ℂ, HasCompactSupport (f : (Fin n → ℝ) → ℂ) → f 0 = 0 → T f = 0 := by
    intro f hf h0
    obtain ⟨R, hR, hs⟩ := hf.isCompact.isBounded.subset_ball_lt 0 0
    let e : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.smulLeft (Units.mk0 R hR.ne')
    have he : ∀ x, e x = R • x := fun _ => rfl
    have he' : ∀ x, e.symm x = R⁻¹ • x := fun x => e.injective (by rw [e.apply_symm_apply, he, smul_inv_smul₀ hR.ne'])
    have := zero_of_ball n (T ∘L SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)
      (fun i f g h => hχ R⁻¹ i _ _ fun x => by
        show g (e.symm x) = _ * f (e.symm x)
        rw [h, he']; simp) (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) ?_ (by
        show f (e 0) = 0
        rw [map_zero, h0])
    · rw [← this]
      exact congrArg T (SchwartzMap.ext fun x => congrArg f (e.apply_symm_apply x).symm)
    · have hsub : Function.support (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) ⊆ e ⁻¹' tsupport f :=
        fun x hx => subset_tsupport _ hx
      refine (closure_minimal hsub ((isClosed_tsupport _).preimage e.continuous)).trans fun x hx => ?_
      have := hs hx
      rw [mem_ball_zero_iff, he, norm_smul, Real.norm_eq_abs, abs_of_pos hR] at this
      rw [mem_ball_zero_iff]
      exact (mul_lt_iff_lt_one_right hR).1 this
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ (b : (Fin n → ℝ) → ℝ)) :=
    b.hasCompactSupport.comp_left rfl
  let ψ : SchwartzMap (Fin n → ℝ) ℂ :=
    h₁.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hψ : ∀ x, ψ x = (b x : ℂ) := fun x => rfl
  have hψ0 : ψ 0 = 1 := by
    rw [hψ, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]; simp
  refine ⟨T ψ, fun f => ?_⟩
  let S : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ :=
    BoundedContinuousFunction.evalCLM ℂ 0 ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ _
  have hcl : IsClosed {f : SchwartzMap (Fin n → ℝ) ℂ | T f = T ψ * S f} :=
    isClosed_eq T.continuous (continuous_const.mul S.continuous)
  refine closure_minimal (t := {f : SchwartzMap (Fin n → ℝ) ℂ | T f = T ψ * S f}) ?_ hcl (dense_hasCompactSupport n f)
  intro f hf
  have := hA (f - f 0 • ψ) (HasCompactSupport.sub hf (HasCompactSupport.smul_left (f := fun _ => f 0) h₁)) (by
    show f 0 - f 0 • ψ 0 = 0
    rw [hψ0]; simp)
  rw [map_sub, map_smul, sub_eq_zero, smul_eq_mul, mul_comm] at this
  exact this

theorem eq_delta' {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →L[ℂ] ℂ)
    (hχ : ∀ (l : V →ₗ[ℝ] ℝ) (f g : SchwartzMap V ℂ), (∀ x, g x = cexp (2 * π * I * l x) * f x) → T g = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap V ℂ, T f = a * f 0 := by
  let e : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := (Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv
  obtain ⟨a, ha⟩ := eq_delta _ (T ∘L SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) fun t i f g h =>
    hχ (t • (LinearMap.proj i ∘ₗ e.toLinearEquiv.toLinearMap)) _ _ fun x => h (e x)
  refine ⟨a, fun f => ?_⟩
  have := ha (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm f)
  refine Eq.trans ?_ (this.trans ?_)
  · exact congrArg T (SchwartzMap.ext fun x => congrArg f (e.symm_apply_apply x).symm)
  · show a * f (e.symm 0) = _
    rw [map_zero]

end Real
end S

open GlobalTheory.AdelicU in
open scoped Classical in
theorem schur (F : Type) [Field F] [NumberField F] [IsTotallyReal F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ) (hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hadm : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ)
    (hT : ∀ w, ∀ Φ ∈ schA F κ, T (schr ψ w Φ) = schr ψ w (T Φ)) :
    ∃ a : ℂ, ∀ Φ ∈ schA F κ, T Φ = a • Φ := by
  letI := fun v : HeightOneSpectrum (𝓞 F) => GlobalTheory.LocalData.complRel v
  have hpm : ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ), ∀ g ∈ SB (κ → Af F), pureA F f g ∈ schA F κ :=
    fun f g hg => Submodule.subset_span ⟨f, g, hg, rfl⟩
  obtain ⟨nd1, -, nd2⟩ := GlobalTheory.GaugeEx.CharLoc.char_local F ψ hψ
  let l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj (0 : κ → AF F) ∘ₗ T
  have hl : l ∈ (adeleClass F).adm κ := hadm _ fun g _ =>
    ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0 ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ _), fun f => by
      show f (fun _ => InfiniteAdeleRing.ringEquiv_mixedSpace F 0) * g 0 = g 0 * f 0
      rw [map_zero, mul_comm]; rfl⟩
  have hmod : ∀ y, ∀ Φ ∈ schA F κ, l (fun x => ψ (x ⬝ᵥ y) * Φ x) = l Φ := fun y Φ hΦ => by
    have e1 : (fun x => ψ (x ⬝ᵥ y) * Φ x) = schr ψ (0, y) Φ := by funext u; simp [schr]
    show T _ 0 = T Φ 0
    rw [e1, hT _ _ hΦ]
    simp [schr]
  let lf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ → ((κ → Af F) → ℂ) →ₗ[ℂ] ℂ := fun f => l ∘ₗ
    { toFun := pureA F f
      map_add' := fun g g' => by funext x; simp [pureA, mul_add]
      map_smul' := fun a g => by funext x; simp [pureA, mul_left_comm] }
  have hfin : ∀ f, ∀ g ∈ SB (κ → Af F), g 0 = 0 → lf f g = 0 := fun f g hg h0 => by
    refine eq_zero_of_mul_invariant (lf f) (Set.range fun p : κ × Σ v, Fv F v => fun u =>
      psiV F ψ p.2.1 (evalV F p.2.1 (u p.1) * p.2.2)) ?_ ?_ hg ?_
    · rintro _ ⟨⟨i, v, c⟩, rfl⟩
      have := GlobalTheory.LocalData.isLocalField v
      have := nonarch_field (Fv F v)
      have h1 := isLocallyConstant_addChar (ψ.compAddMonoidHom
        ((LinearMap.inr F (Ainf F) (Af F) ∘ₗ singleFin v).toAddMonoidHom))
        (hψ.1.comp (continuous_const.prodMk (continuous_singleFin v)))
      exact h1.comp_continuous (((RestrictedProduct.continuous_eval v).comp (continuous_apply i)).mul continuous_const)
    · rintro _ ⟨⟨i, v, c⟩, rfl⟩ g hg
      rw [show lf f g = l (pureA F f g) from rfl, ← hmod (Pi.single i (pairA F 0 (singleV F v c))) _ (hpm f g hg)]
      refine congrArg l (funext fun x => ?_)
      have e : x i * pairA F 0 (singleV F v c) = pairA F 0 (singleV F v (evalV F v (x i).2 * c)) := by
        refine Prod.ext (mul_zero _) (af_ext fun u => ?_)
        show evalV F u ((x i).2 * singleFin v c) = evalV F u (singleFin v _)
        by_cases h : u = v
        · subst h; rw [map_mul, evalV_singleFin_self, evalV_singleFin_self]
        · rw [map_mul, evalV_singleFin_ne h, evalV_singleFin_ne h, mul_zero]
      rw [dotProduct_single, e]
      exact mul_left_comm _ _ _
    · intro u hu
      obtain ⟨i, hi⟩ := Function.ne_iff.1 (show u ≠ 0 from fun e => hu (e ▸ h0))
      obtain ⟨v, hv⟩ : ∃ v, evalV F v (u i) ≠ 0 := by
        by_contra h
        push Not at h
        exact hi (af_ext fun v => (h v).trans (map_zero _).symm)
      obtain ⟨y, hy⟩ := nd1 v
      refine ⟨_, ⟨⟨i, v, y / evalV F v (u i)⟩, rfl⟩, ?_⟩
      show psiV F ψ v _ ≠ 1
      rwa [mul_div_cancel₀ _ hv]
  let r := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have hst : ∀ a : Ainf F, ψ (pairA F a 0) = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (r a) : ℝ)) := fun a =>
    hstd.2.2 _ fun u hu => Prod.ext (by
      show u.1 * a = 0
      rw [(map_eq_zero_iff _ r.injective).1 hu, zero_mul]) (mul_zero _)
  let β : LinearMap.BilinForm ℝ (κ → mixedEmbedding.mixedSpace F) := LinearMap.mk₂ ℝ
    (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y))
    (fun _ _ _ => by rw [add_dotProduct, map_add]) (fun _ _ _ => by rw [smul_dotProduct, map_smul])
    (fun _ _ _ => by rw [dotProduct_add, map_add]) (fun _ _ _ => by rw [dotProduct_smul, map_smul])
  have hβ : Function.Surjective β := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1
      ((injective_iff_map_eq_zero _).2 fun x hx => funext fun i => ?_)
    refine (map_eq_zero_iff _ r.symm.injective).1 (nd2 _ fun y => ?_)
    have := LinearMap.congr_fun hx (Pi.single i (r y))
    simp only [β, LinearMap.mk₂_apply, dotProduct_single, LinearMap.zero_apply] at this
    rw [psiInf, hst, map_mul, r.apply_symm_apply, this]; simp
  have hinf : ∀ g ∈ SB (κ → Af F), ∃ a : ℂ, ∀ f, lf f g = a * f 0 := fun g hg => by
    obtain ⟨T₀, hT₀⟩ := hl g hg
    obtain ⟨a, ha⟩ := S.eq_delta' T₀ fun m f f' h => by
      obtain ⟨y, rfl⟩ := hβ (-m) |>.imp fun y hy => (neg_eq_iff_eq_neg.2 hy : -β y = m)
      rw [← hT₀, ← hT₀, ← hmod (fun i => pairA F (r.symm (y i)) 0) _ (hpm f g hg)]
      refine congrArg l (funext fun x => ?_)
      have e : (x ⬝ᵥ fun i => pairA F (r.symm (y i)) 0) = pairA F (r.symm (y ⬝ᵥ fun i => r (x i).1)) 0 := by
        refine Prod.ext ?_ ?_
        · show fstA F _ = r.symm _
          simp only [dotProduct, map_sum, map_mul, r.symm_apply_apply]
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
        · show sndA F _ = 0
          simp only [dotProduct, map_sum, map_mul]
          exact Finset.sum_eq_zero fun i _ => mul_zero _
      rw [e, hst, r.apply_symm_apply, pureA, pureA, h, mul_assoc _ (f _)]
      refine congrArg₂ (· * ·) (congrArg Complex.exp ?_) rfl
      simp only [β, LinearMap.neg_apply, LinearMap.mk₂_apply, Complex.ofReal_neg, mul_neg, neg_mul]
      rfl
    exact ⟨a, fun f => (hT₀ f).trans (ha f)⟩
  obtain ⟨a, ha⟩ : ∃ a : ℂ, ∀ f, ∀ g ∈ SB (κ → Af F), lf f g = a * (f 0 * g 0) := by
    by_cases h : ∃ g ∈ SB (κ → Af F), g 0 ≠ 0
    · obtain ⟨g₀, h0, h1⟩ := h
      obtain ⟨a, ha⟩ := hinf g₀ h0
      refine ⟨a / g₀ 0, fun f g hg => ?_⟩
      have := hfin f _ (sub_mem hg (Submodule.smul_mem _ (g 0 / g₀ 0) h0)) (by simp [h1])
      rw [map_sub, map_smul, sub_eq_zero, ha] at this
      rw [this, smul_eq_mul]; ring
    · push Not at h
      exact ⟨0, fun f g hg => by rw [hfin f g hg (h g hg), zero_mul]⟩
  refine ⟨a, fun Φ hΦ => funext fun x => ?_⟩
  have h4 : l (schr ψ (x, 0) Φ) = T Φ x := by
    show T _ 0 = _
    rw [hT _ _ hΦ]; simp [schr]
  rw [← h4]
  clear h4
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    have := ha (SchwartzMap.compSubConstCLM ℂ (-fun i => r (x i).1) f) (fun u => g (u + fun i => (x i).2))
      ⟨hg.1.comp_continuous (continuous_add_const _), hg.2.comp_homeomorph (Homeomorph.addRight _)⟩
    refine Eq.trans (congrArg l (funext fun u => ?_)) (this.trans ?_)
    · simp only [schr, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
      refine congrArg₂ (· * ·) (congrArg f (funext fun i => ?_)) rfl
      exact (map_add r _ _).trans (sub_neg_eq_add _ _).symm
    · simp [pureA, r]
  | zero =>
    rw [show schr ψ (x, 0) 0 = 0 from funext fun _ => mul_zero _, map_zero]; simp
  | add Φ Ψ _ _ h h' =>
    rw [show schr ψ (x, 0) (Φ + Ψ) = schr ψ (x, 0) Φ + schr ψ (x, 0) Ψ from funext fun _ => mul_add _ _ _, map_add, h, h']
    simp [mul_add]
  | smul c Φ _ h =>
    rw [show schr ψ (x, 0) (c • Φ) = c • schr ψ (x, 0) Φ from funext fun _ => mul_left_comm _ _ _, map_smul, h]
    simp [mul_left_comm]

end PositivityTheory.Member.ZakTransform
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (pure tens SInf evI At Rest Acts piW)
open GlobalTheory.EmbChart (atPlace atPlace_mul_right evFin_atPlace)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace PositivityTheory.Member.ZakTransform

section Tens
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def stdF (κ : Type) (u : HeightOneSpectrum (𝓞 F)) : (κ → Fv F u) → ℂ :=
  Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1

def Good (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) : Prop :=
  (∀ u, φ u ∈ SB (κ → Fv F u)) ∧ ∀ᶠ u in cofinite, φ u = stdF κ u

def pf (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) (y : κ → Af F) : ℂ :=
  ∏ᶠ u, φ u fun i => evalV F u (y i)

theorem ev_int (y : κ → Af F) : ∀ᶠ u in cofinite, ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F :=
  eventually_all.2 fun i => (y i).2

theorem cont_evalV (u : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F u) :=
  (continuous_apply u).comp RestrictedProduct.continuous_coe

theorem isOpen_intAf : IsOpen {a : Af F | ∀ v, evalV F v a ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

theorem isOpen_intV (u : HeightOneSpectrum (𝓞 F)) : IsOpen {x : κ → Fv F u | ∀ i, x i ∈ u.adicCompletionIntegers F} := by
  simp only [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i => (Valued.isOpen_valuationSubring _).preimage (continuous_apply i)

theorem isCompact_intV (u : HeightOneSpectrum (𝓞 F)) :
    IsCompact {x : κ → Fv F u | ∀ i, x i ∈ u.adicCompletionIntegers F} := by
  have h : IsCompact (u.adicCompletionIntegers F : Set (Fv F u)) := isCompact_iff_compactSpace.2
    (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F u)
  simpa [Set.pi] using isCompact_univ_pi fun _ : κ => h

def intV (κ : Type) [Fintype κ] (u : HeightOneSpectrum (𝓞 F)) : OpenAddSubgroup (κ → Fv F u) where
  carrier := {x | ∀ i, x i ∈ u.adicCompletionIntegers F}
  add_mem' h h' i := add_mem (h i) (h' i)
  zero_mem' _ := zero_mem _
  neg_mem' h i := neg_mem (h i)
  isOpen' := isOpen_intV u

theorem stdF_mem (u : HeightOneSpectrum (𝓞 F)) : stdF κ u ∈ SB (κ → Fv F u) :=
  GlobalTheory.WeilM.HaarUniq.indicator_mem (intV κ u) (isCompact_intV u)

theorem good_std : Good (stdF (F := F) κ) := ⟨stdF_mem, .of_forall fun _ => rfl⟩

theorem isCompact_box (C : ∀ u : HeightOneSpectrum (𝓞 F), Set (Fv F u)) (hC : ∀ u, IsCompact (C u))
    (h : ∀ᶠ u in cofinite, C u ⊆ u.adicCompletionIntegers F) : IsCompact {a : Af F | ∀ u, evalV F u a ∈ C u} := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {u | C u ⊆ u.adicCompletionIntegers F}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 h
  let P := RestrictedProduct (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (𝓟 S)
  have h1 : IsCompact {x : P | ∀ u, x u ∈ C u} := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    convert isCompact_univ_pi hC
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ u -
      exact hy u
    · intro hx
      exact ⟨⟨x, fun u hu => hu (hx u trivial)⟩, fun u => hx u trivial, rfl⟩
  have h2 := h1.image (RestrictedProduct.continuous_inclusion hS)
  have e : {a : Af F | ∀ u, evalV F u a ∈ C u} = RestrictedProduct.inclusion _ _ hS '' {x : P | ∀ u, x u ∈ C u} := by
    ext a
    constructor
    · intro ha
      exact ⟨⟨a.1, fun u hu => hu (ha u)⟩, ha, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [e]
  exact h2

theorem pf_eq_prod {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (S : Finset (HeightOneSpectrum (𝓞 F)))
    (y : κ → Af F) (h : ∀ u ∉ S, φ u = stdF κ u ∧ ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F) :
    pf φ y = ∏ u ∈ S, φ u fun i => evalV F u (y i) := by
  refine finprod_eq_prod_of_mulSupport_subset _ fun u hu => ?_
  by_contra hn
  apply hu
  simp only
  rw [(h u hn).1, stdF, Set.indicator_of_mem (by exact (h u hn).2)]
  rfl

theorem exists_fin {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : ∀ᶠ u in cofinite, φ u = stdF κ u)
    (y : κ → Af F) : ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ u ∉ S, φ u = stdF κ u ∧ ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F :=
  ⟨(hφ.and (ev_int y)).toFinset, fun u hu => by
    by_contra hn
    exact hu (Set.Finite.mem_toFinset _ |>.2 hn)⟩

theorem pf_mem {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : Good φ) : pf φ ∈ SB (κ → Af F) := by
  have hc : ∀ u, Continuous fun (y : κ → Af F) i => evalV F u (y i) := fun u =>
    continuous_pi fun i => (cont_evalV u).comp (continuous_apply i)
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨S, hS⟩ := exists_fin hφ.2 x
    have h1 : ∀ᶠ y in 𝓝 x, ∀ i v, evalV F v (y i - x i) ∈ v.adicCompletionIntegers F :=
      eventually_all.2 fun i => (isOpen_intAf.preimage (f := fun y : κ → Af F => y i - x i) (by fun_prop)).mem_nhds
        (by intro v; simp)
    have h2 : ∀ᶠ y in 𝓝 x, ∀ u ∈ S, φ u (fun i => evalV F u (y i)) = φ u fun i => evalV F u (x i) :=
      (eventually_all_finset S).2 fun u _ => ((hφ.1 u).1.comp_continuous (hc u)).eventually_eq x
    filter_upwards [h1, h2] with y h1 h2
    rw [pf_eq_prod S x hS, pf_eq_prod S y fun u hu => ⟨(hS u hu).1, fun i => ?_⟩]
    · exact Finset.prod_congr rfl h2
    · have := add_mem (h1 i u) ((hS u hu).2 i)
      rwa [map_sub, sub_add_cancel] at this
  · have hK : ∀ i : κ, IsCompact {a : Af F | ∀ u, evalV F u a ∈ (fun x => x i) '' tsupport (φ u)} := fun i =>
      isCompact_box _ (fun u => (hφ.1 u).2.isCompact.image (continuous_apply i)) (by
        filter_upwards [hφ.2] with u hu
        rintro _ ⟨x, hx, rfl⟩
        rw [hu] at hx
        exact closure_minimal Set.support_indicator_subset (isCompact_intV u).isClosed hx i)
    refine HasCompactSupport.intro (isCompact_univ_pi hK) fun y hy => ?_
    by_contra h0
    refine hy fun i _ u => ⟨fun i => evalV F u (y i), subset_tsupport _ (fun h => h0 ?_), rfl⟩
    obtain ⟨S, hS⟩ := exists_fin hφ.2 y
    classical
    rw [pf_eq_prod (insert u S) y fun v hv => hS v fun h => hv (Finset.mem_insert_of_mem h)]
    exact Finset.prod_eq_zero (Finset.mem_insert_self _ _) h

theorem pure_mem (f : SInf F κ) {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : Good φ) :
    pure f φ ∈ schA F κ := Submodule.subset_span ⟨f, pf φ, pf_mem hφ, rfl⟩

def box (K : ∀ u : HeightOneSpectrum (𝓞 F), OpenAddSubgroup (κ → Fv F u)) (h : ∀ᶠ u in cofinite, K u = intV κ u)
    (h' : ∀ u, K u ≤ intV κ u) : OpenAddSubgroup (κ → Af F) where
  carrier := {y | ∀ u, (fun i => evalV F u (y i)) ∈ K u}
  add_mem' {a b} ha hb u := by
    have := add_mem (ha u) (hb u)
    simp only [Pi.add_apply, map_add]
    exact this
  zero_mem' u := by
    simp only [Pi.zero_apply, map_zero]
    exact zero_mem (K u)
  neg_mem' {a} ha u := by
    have := neg_mem (ha u)
    simp only [Pi.neg_apply, map_neg]
    exact this
  isOpen' := by
    have e : {y : κ → Af F | ∀ u, (fun i => evalV F u (y i)) ∈ K u} =
        (⋂ i, {y | ∀ v, evalV F v (y i) ∈ v.adicCompletionIntegers F}) ∩
          ⋂ u ∈ {u | ¬ K u = intV κ u}, {y | (fun i => evalV F u (y i)) ∈ K u} := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun H => ⟨fun i v => h' v (H v) i, fun u _ => H u⟩, fun H u => ?_⟩
      by_cases hu : K u = intV κ u
      · rw [hu]; exact fun i => H.1 i u
      · exact H.2 u hu
    rw [e]
    exact (isOpen_iInter_of_finite fun i => isOpen_intAf.preimage (continuous_apply i)).inter
      (Set.Finite.isOpen_biInter h fun u _ => (K u).isOpen.preimage
        (continuous_pi fun i => (cont_evalV u).comp (continuous_apply i)))

theorem exists_box {W : Set (κ → Af F)} (hW : W ∈ 𝓝 0) : ∃ K h h', ((box (F := F) (κ := κ) K h h' : OpenAddSubgroup (κ → Af F)) : Set (κ → Af F)) ⊆ W := by
  classical
  let j : (∀ u : HeightOneSpectrum (𝓞 F), intV κ u) → κ → Af F := fun x i =>
    RestrictedProduct.structureMap (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) cofinite fun u => ⟨(x u).1 i, (x u).2 i⟩
  have hj : Continuous j := continuous_pi fun i => RestrictedProduct.isEmbedding_structureMap.continuous.comp
    (continuous_pi fun u => Continuous.subtype_mk (f := fun x : ∀ u, intV κ u => (x u).1 i) ((continuous_apply i).comp
      ((continuous_subtype_val (p := fun x => x ∈ intV κ u)).comp (continuous_apply (A := fun u => intV κ u) u))) _)
  have h0 : j ⁻¹' W ∈ 𝓝 0 := hj.continuousAt.preimage_mem_nhds (by convert hW; rfl)
  rw [nhds_pi, Filter.mem_pi] at h0
  obtain ⟨I, hI, t, ht, hs⟩ := h0
  have : ∀ u, ∃ K : OpenAddSubgroup (κ → Fv F u), ∀ x : intV κ u, x.1 ∈ K → x ∈ t u := fun u => by
    have := ht u
    rw [nhds_subtype, mem_comap] at this
    obtain ⟨s, hs, hst⟩ := this
    obtain ⟨K, hK⟩ := (nonarch_pi (Fv F u) κ).is_nonarchimedean s hs
    exact ⟨K, fun x hx => hst (hK hx)⟩
  choose K hK using this
  refine ⟨fun u => if u ∈ I then K u ⊓ intV κ u else intV κ u, ?_, fun u => ?_, fun y hy => ?_⟩
  · filter_upwards [hI.compl_mem_cofinite] with u hu using if_neg hu
  · simp only
    split_ifs
    · exact inf_le_right
    · exact le_rfl
  · have h1 : ∀ u, (fun i => evalV F u (y i)) ∈ intV κ u := fun u => by
      have := hy u
      simp only at this
      split_ifs at this
      · exact this.2
      · exact this
    refine hs (a := fun u => ⟨_, h1 u⟩) fun u hu => hK u _ ?_
    have := hy u
    simp only [if_pos hu] at this
    exact this.1

theorem mem_span_pf {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    g ∈ Submodule.span ℂ {h | ∃ φ, Good φ ∧ h = pf φ} := by
  haveI : NonarchimedeanAddGroup (κ → Af F) := ⟨fun W hW => by
    obtain ⟨K, h, h', hs⟩ := exists_box hW
    exact ⟨_, hs⟩⟩
  obtain ⟨K₀, hK₀⟩ := GlobalTheory.WeilM.HaarUniq.exists_invariant hg
  obtain ⟨K, h, h', hs⟩ := exists_box K₀.mem_nhds_zero
  obtain ⟨S, hS⟩ := GlobalTheory.WeilM.HaarUniq.exists_decomp (box K h h') hg.2 fun k hk => hK₀ k (hs hk)
  rw [hS]
  refine Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  generalize q.out = a
  have hG : Good fun u x => Set.indicator (K u : Set (κ → Fv F u)) (fun _ => (1 : ℂ)) (x + -fun i => evalV F u (a i)) := by
    constructor
    · intro u
      have := GlobalTheory.WeilM.HaarUniq.indicator_mem (K u) ((isCompact_intV u).of_isClosed_subset (K u).isClosed (h' u))
      exact ⟨this.1.comp_continuous (continuous_add_const _), this.2.comp_homeomorph (Homeomorph.addRight _)⟩
    · filter_upwards [h, ev_int a] with u hu ha
      funext x
      rw [hu]
      have ha' : (-fun i => evalV F u (a i)) ∈ intV κ u := neg_mem (show _ ∈ intV κ u from ha)
      by_cases hx : x ∈ intV κ u
      · rw [Set.indicator_of_mem (add_mem hx ha'), stdF, Set.indicator_of_mem (by exact hx)]; rfl
      · rw [Set.indicator_of_notMem (by rwa [SetLike.mem_coe, add_mem_cancel_right ha']), stdF,
          Set.indicator_of_notMem (by exact hx)]
  refine ⟨_, hG, funext fun y => ?_⟩
  have e : ∀ u, ((fun i => evalV F u (y i)) + -fun i => evalV F u (a i)) = fun i => evalV F u ((y + -a) i) := fun u => by
    funext i; simp
  by_cases hy : y + -a ∈ box K h h'
  · rw [Set.indicator_of_mem (by exact hy), pf, eq_comm]
    refine finprod_eq_one_of_forall_eq_one fun u => ?_
    rw [e, Set.indicator_of_mem (by exact hy u)]
  · rw [Set.indicator_of_notMem (by exact hy)]
    obtain ⟨u, hu⟩ := not_forall.1 hy
    obtain ⟨S, hS⟩ := exists_fin hG.2 y
    classical
    rw [pf_eq_prod (insert u S) y fun v hv => hS v fun h => hv (Finset.mem_insert_of_mem h), eq_comm]
    refine Finset.prod_eq_zero (Finset.mem_insert_self _ _) ?_
    rw [e, Set.indicator_of_notMem (by exact hu)]

theorem pureA_add (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g h : (κ → Af F) → ℂ) :
    pureA F f (g + h) = pureA F f g + pureA F f h := funext fun _ => mul_add _ _ _

theorem pureA_smul (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (c : ℂ) (g : (κ → Af F) → ℂ) :
    pureA F f (c • g) = c • pureA F f g := funext fun _ => mul_left_comm _ _ _

theorem pureA_zero (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) : pureA F f (0 : (κ → Af F) → ℂ) = 0 :=
  funext fun _ => mul_zero _

theorem schA_le : schA F κ ≤ Submodule.span ℂ {Φ | ∃ f φ, Good φ ∧ Φ = pure f φ} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  have := mem_span_pf hg
  clear hg
  induction this using Submodule.span_induction with
  | mem x hx => obtain ⟨φ, hφ, rfl⟩ := hx; exact Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  | zero => rw [pureA_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [pureA_add]; exact add_mem hx hy
  | smul a x _ hx => rw [pureA_smul]; exact Submodule.smul_mem _ _ hx

end Tens

section Lift
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : HeightOneSpectrum (𝓞 F))

def off (a : AF F) : AF F := a - atPlace v (evFin F v a)

theorem ev_off (a : AF F) : evFin F v (off v a) = 0 := by simp [off, evFin_atPlace]

theorem off_at (t : Fv F v) : off v (atPlace v t) = 0 := by simp [off, evFin_atPlace]

theorem off_add (a b : AF F) : off v (a + b) = off v a + off v b := by simp only [off, map_add]; ring

theorem off_mul (a b : AF F) : off v (a * b) = a * off v b := by
  rw [off, off, mul_sub, mul_comm a (atPlace v _), atPlace_mul_right, map_mul, mul_comm (evFin F v a)]

theorem off_off (a : AF F) : off v (off v a) = off v a := by rw [off, ev_off, map_zero, sub_zero]

theorem at_mul_off (t : Fv F v) (a : AF F) : atPlace v t * off v a = 0 := by
  rw [atPlace_mul_right, ev_off, mul_zero, map_zero]

theorem off_add_at (a : AF F) : off v a + atPlace v (evFin F v a) = a := sub_add_cancel _ _

theorem off_dot (x y : κ → AF F) : off v (x ⬝ᵥ y) = x ⬝ᵥ fun i => off v (y i) := by
  simp only [off, dotProduct, map_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => off_mul v _ _

theorem ev_dot (x y : κ → AF F) : evFin F v (x ⬝ᵥ y) = (fun i => evFin F v (x i)) ⬝ᵥ fun i => evFin F v (y i) := by
  simp only [dotProduct, map_sum, map_mul]

def Indep (r : (κ → AF F) → ℂ) : Prop := ∀ x (t : κ → Fv F v), r (x + fun i => atPlace v (t i)) = r x

def liftG {X Y : Type} (a : X → Y → X) (p : X → Y) (S : Module.End ℂ (Y → ℂ)) : Module.End ℂ (X → ℂ) where
  toFun Ψ x := S (fun t => Ψ (a x t)) (p x)
  map_add' Ψ Ψ' := funext fun x => congrFun (map_add S (fun t => Ψ (a x t)) (fun t => Ψ' (a x t))) _
  map_smul' c Ψ := funext fun x => congrFun (map_smul S c (fun t => Ψ (a x t))) _

def lift (S : Module.End ℂ ((κ → Fv F v) → ℂ)) : Module.End ℂ ((κ → AF F) → ℂ) :=
  liftG (fun x t i => off v (x i) + atPlace v (t i)) (fun x i => evFin F v (x i)) S

theorem lift_apply (S : Module.End ℂ ((κ → Fv F v) → ℂ)) (Ψ : (κ → AF F) → ℂ) (x : κ → AF F) : lift v S Ψ x =
    S (fun t => Ψ fun i => off v (x i) + atPlace v (t i)) fun i => evFin F v (x i) := rfl

variable {v}

theorem Indep.off {r : (κ → AF F) → ℂ} (h : Indep v r) (x : κ → AF F) : r (fun i => off v (x i)) = r x := by
  rw [← h _ fun i => evFin F v (x i)]
  congr 1
  funext i
  exact off_add_at v _

theorem lift_tens (S : Module.End ℂ ((κ → Fv F v) → ℂ)) (φ : (κ → Fv F v) → ℂ) {r : (κ → AF F) → ℂ} (h : Indep v r) :
    lift v S (tens (evFin F v) φ r) = tens (evFin F v) (S φ) r := by
  funext x
  have e : (fun t => tens (evFin F v) φ r fun i => off v (x i) + atPlace v (t i)) = r x • φ := by
    funext t
    have := h (fun i => off v (x i)) t
    rw [h.off] at this
    simp only [tens, map_add, ev_off, evFin_atPlace, zero_add, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]
    exact congrArg (· * φ t) this
  rw [lift_apply, e, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  rfl

open Classical in
theorem pure_update (f : SInf F κ) {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ}
    (hφ : ∀ᶠ u in cofinite, φ u = stdF κ u) (φ' : (κ → Fv F v) → ℂ) :
    pure f (Function.update φ v φ') = tens (evFin F v) φ' (pure f (Function.update φ v 1)) := by
  funext x
  obtain ⟨S, hS⟩ := exists_fin hφ fun i => sndA F (x i)
  have key : ∀ φ'' : (κ → Fv F v) → ℂ, pf (Function.update φ v φ'') (fun i => sndA F (x i)) =
      φ'' (fun i => evFin F v (x i)) * ∏ u ∈ S.erase v, φ u fun i => evFin F u (x i) := fun φ'' => by
    rw [pf_eq_prod (insert v (S.erase v)) _ fun u hu => ?_, Finset.prod_insert (Finset.notMem_erase _ _),
      Function.update_self]
    · congr 1
      refine Finset.prod_congr rfl fun u hu => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hu)]
      rfl
    · have h1 : u ≠ v := fun e => hu (e ▸ Finset.mem_insert_self _ _)
      rw [Function.update_of_ne h1]
      exact hS u fun h => hu (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h1, h⟩))
  show f _ * pf _ (fun i => sndA F (x i)) = φ' _ * (f _ * pf _ (fun i => sndA F (x i)))
  rw [key, key, Pi.one_apply]
  ring

open Classical in
theorem indep_pure (f : SInf F κ) (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) :
    Indep v (pure f (Function.update φ v 1)) := by
  intro x t
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  congr 1
  · congr 1
    funext i
    show _ = evI F (x i)
    unfold evI
    congr 1
    exact add_zero _
  · refine finprod_congr fun u => ?_
    by_cases h : u = v
    · subst h; simp
    · refine congrArg _ (funext fun i => ?_)
      rw [Pi.add_apply, map_add]
      exact add_eq_left.2 (evalV_singleFin_ne h _)

open Classical in
theorem Good.update {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : Good φ) {φ' : (κ → Fv F v) → ℂ}
    (h : φ' ∈ SB (κ → Fv F v)) : Good (Function.update φ v φ') := by
  refine ⟨fun u => ?_, ?_⟩
  · by_cases e : u = v
    · subst e; rwa [Function.update_self]
    · rw [Function.update_of_ne e]; exact hφ.1 u
  · filter_upwards [hφ.2, (Set.finite_singleton v).compl_mem_cofinite] with u hu e
    rwa [Function.update_of_ne e]

open Classical in
theorem lift_pure (S : Module.End ℂ ((κ → Fv F v) → ℂ)) (f : SInf F κ)
    {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : Good φ) :
    lift v S (pure f φ) = pure f (Function.update φ v (S (φ v))) := by
  conv_lhs => rw [← Function.update_eq_self v φ]
  rw [pure_update f hφ.2, pure_update f hφ.2 (S _), lift_tens _ _ (indep_pure f φ)]

theorem schA_ind {P : ((κ → AF F) → ℂ) → Prop} (h0 : P 0) (h1 : ∀ x y, P x → P y → P (x + y))
    (h2 : ∀ (c : ℂ) x, P x → P (c • x)) (h : ∀ f φ, Good φ → P (pure f φ)) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : P Φ := by
  have := schA_le hΦ
  clear hΦ
  induction this using Submodule.span_induction with
  | mem x hx => obtain ⟨f, φ, hφ, rfl⟩ := hx; exact h f φ hφ
  | zero => exact h0
  | add x y _ _ hx hy => exact h1 _ _ hx hy
  | smul a x _ hx => exact h2 _ _ hx

theorem lift_mem {S : Module.End ℂ ((κ → Fv F v) → ℂ)} (hS : ∀ φ ∈ SB (κ → Fv F v), S φ ∈ SB (κ → Fv F v))
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : lift v S Φ ∈ schA F κ := by
  refine schA_ind (P := fun Φ => lift v S Φ ∈ schA F κ) (by simp) (fun x y hx hy => ?_) (fun c x hx => ?_)
    (fun f φ hφ => ?_) hΦ
  · rw [map_add]; exact add_mem hx hy
  · rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · rw [lift_pure S f hφ]; exact pure_mem f (hφ.update (hS _ (hφ.1 v)))

theorem lift_adm {S : Module.End ℂ ((κ → Fv F v) → ℂ)} (hS : ∀ φ ∈ SB (κ → Fv F v), S φ ∈ SB (κ → Fv F v)) :
    ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ lift v S ∈ (adeleClass F).adm κ := by
  intro l hl g hg
  have : ∃ g' ∈ SB (κ → Af F), ∀ f : SInf F κ, lift v S (pureA F f g) = pureA F f g' := by
    have := mem_span_pf hg
    clear hg
    induction this using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, hφ, rfl⟩ := hx
      exact ⟨_, pf_mem (hφ.update (hS _ (hφ.1 v))), fun f => lift_pure S f hφ⟩
    | zero => exact ⟨0, zero_mem _, fun f => by rw [pureA_zero, map_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨b, hb, hy⟩ := hy
      exact ⟨a + b, add_mem ha hb, fun f => by rw [pureA_add, map_add, hx, hy, pureA_add]⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, hx⟩ := hx
      exact ⟨c • a, Submodule.smul_mem _ _ ha, fun f => by rw [pureA_smul, map_smul, hx, pureA_smul]⟩
  obtain ⟨g', hg', h⟩ := this
  obtain ⟨T, hT⟩ := hl g' hg'
  exact ⟨T, fun f => by rw [LinearMap.comp_apply, h, hT]⟩

theorem lift_lift {S S' : Module.End ℂ ((κ → Fv F v) → ℂ)} (hS : ∀ φ ∈ SB (κ → Fv F v), S' φ ∈ SB (κ → Fv F v))
    {S'' : Module.End ℂ ((κ → Fv F v) → ℂ)} (h : ∀ φ ∈ SB (κ → Fv F v), S (S' φ) = S'' φ)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : lift v S (lift v S' Φ) = lift v S'' Φ := by
  classical
  refine schA_ind (P := fun Φ => lift v S (lift v S' Φ) = lift v S'' Φ) (by simp) (fun x y hx hy => ?_)
    (fun c x hx => ?_) (fun f φ hφ => ?_) hΦ
  · simp only [map_add, hx, hy]
  · simp only [map_smul, hx]
  · rw [lift_pure S' f hφ, lift_pure S f (hφ.update (hS _ (hφ.1 v))), lift_pure S'' f hφ, Function.update_self,
      Function.update_idem, h _ (hφ.1 v)]

theorem lift_one (Φ : (κ → AF F) → ℂ) : lift v 1 Φ = Φ := funext fun x => by
  rw [lift_apply]
  exact congrArg Φ (funext fun i => off_add_at v _)

variable (v) in

def psv (ψ : AddChar (AF F) ℂ) : AddChar (Fv F v) ℂ := ψ.compAddMonoidHom (atPlace v).toAddMonoidHom

theorem psv_apply (ψ : AddChar (AF F) ℂ) (t : Fv F v) : psv v ψ t = ψ (atPlace v t) := rfl

scoped instance invTwoV : Invertible (2 : Fv F v) :=
  ⟨evFin F v (⅟2), by rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one],
    by rw [← map_ofNat (evFin F v) 2, ← map_mul, mul_invOf_self, map_one]⟩

variable (v) in

def evP (w : (κ → AF F) × (κ → AF F)) : (κ → Fv F v) × (κ → Fv F v) := (fun i => evFin F v (w.1 i), fun i => evFin F v (w.2 i))

variable (v) in

def offP (w : (κ → AF F) × (κ → AF F)) : (κ → AF F) × (κ → AF F) := (fun i => off v (w.1 i), fun i => off v (w.2 i))

theorem schr_tens (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) (φ : (κ → Fv F v) → ℂ) {r : (κ → AF F) → ℂ}
    (h : Indep v r) : schr ψ w (tens (evFin F v) φ r) =
      tens (evFin F v) (schr (psv v ψ) (evP v w) φ) (schr ψ (offP v w) r) := by
  funext x
  have e1 : r (x + w.1) = r (x + (offP v w).1) := by
    rw [← h (x + (offP v w).1) fun i => evFin F v (w.1 i)]
    congr 1
    funext i
    simp only [Pi.add_apply, offP, add_assoc, off_add_at]
  have e2 : ψ (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) =
      psv v ψ ((fun i => evFin F v (x i)) ⬝ᵥ (evP v w).2 + ⅟(2 : Fv F v) * ((evP v w).1 ⬝ᵥ (evP v w).2)) *
      ψ (x ⬝ᵥ (offP v w).2 + ⅟(2 : AF F) * ((offP v w).1 ⬝ᵥ (offP v w).2)) := by
    rw [psv_apply, ← AddChar.map_add_eq_mul, ← off_add_at v (x ⬝ᵥ w.2 + _), add_comm (off v _)]
    congr 2
    · rw [map_add, map_mul, ev_dot, ev_dot]; rfl
    · rw [off_add, off_mul, off_dot, ← off_off v (w.1 ⬝ᵥ w.2), off_dot v w.1 w.2, dotProduct_comm w.1, off_dot,
        dotProduct_comm (fun i => off v (w.2 i))]
      rfl
  simp only [schr, tens]
  rw [e1, e2]
  simp only [Pi.add_apply, map_add]
  show _ = _ * φ (fun i => evFin F v (x i) + evFin F v (w.1 i)) * _
  ring

theorem Indep.schr (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) {r : (κ → AF F) → ℂ}
    (h : Indep v r) : Indep v (schr ψ (offP v w) r) := by
  intro x t
  simp only [GlobalTheory.WeilM.schr]
  rw [add_right_comm, h, add_dotProduct]
  congr 3
  refine add_eq_left.2 (Finset.sum_eq_zero fun i _ => at_mul_off v _ _)

theorem schr_add {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R))
    (φ φ' : (κ → R) → ℂ) : schr ψ w (φ + φ') = schr ψ w φ + schr ψ w φ' := funext fun _ => mul_add _ _ _

theorem schr_smul {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R))
    (c : ℂ) (φ : (κ → R) → ℂ) : schr ψ w (c • φ) = c • schr ψ w φ := funext fun _ => mul_left_comm _ _ _

theorem schr_zero {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (φ : (κ → R) → ℂ) :
    schr ψ 0 φ = φ := funext fun x => by simp [schr]

theorem lift_schr (ψ : AddChar (AF F) ℂ) {S : Module.End ℂ ((κ → Fv F v) → ℂ)} {w w' : (κ → AF F) × (κ → AF F)}
    (h : offP v w = offP v w')
    (hS : ∀ φ ∈ SB (κ → Fv F v), S (schr (psv v ψ) (evP v w) φ) = schr (psv v ψ) (evP v w') (S φ))
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : lift v S (schr ψ w Φ) = schr ψ w' (lift v S Φ) := by
  classical
  refine schA_ind (P := fun Φ => lift v S (schr ψ w Φ) = schr ψ w' (lift v S Φ)) ?_ (fun x y hx hy => ?_)
    (fun c x hx => ?_) (fun f φ hφ => ?_) hΦ
  · have : ∀ w, schr ψ w (0 : (κ → AF F) → ℂ) = 0 := fun w => funext fun _ => mul_zero _
    simp only [this, map_zero]
  · simp only [map_add, schr_add, hx, hy]
  · simp only [map_smul, schr_smul, hx]
  · have hi := indep_pure (v := v) f φ
    rw [← Function.update_eq_self v φ, pure_update f hφ.2, schr_tens ψ w _ hi, lift_tens _ _ (hi.schr ψ w),
      lift_tens _ _ hi, schr_tens ψ w' _ hi, h, hS _ (hφ.1 v)]

theorem schr_mem_SB {ψ : AddChar (Fv F v) ℂ} (hψ : Continuous ψ) (w : (κ → Fv F v) × (κ → Fv F v))
    {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) : schr ψ w φ ∈ SB (κ → Fv F v) := by
  haveI := nonarch_field (Fv F v)
  refine ⟨IsLocallyConstant.mul ((isLocallyConstant_addChar ψ hψ).comp_continuous (by fun_prop))
    (hφ.1.comp_continuous (continuous_add_const _)), HasCompactSupport.mul_left ?_⟩
  exact hφ.2.comp_homeomorph (Homeomorph.addRight _)

end Lift

section Split
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE cA incM UA Spc Model Rep mat HasSig)
open GlobalTheory.EmbChart (tensAt compFin_tensAt tensAt_mul_right tensAt_tmul)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)}

theorem hasSig_det {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  intro h0
  have e : (A.submatrix id finSumFinEquiv.symm)ᵀ * M * (A.map star).submatrix id finSumFinEquiv.symm =
      (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; rfl
  have := congrArg det e
  rw [det_mul, det_mul, h0, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_neg] at this
  simp only [mul_zero, zero_mul, det_one, one_mul, mul_one] at this
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) this.symm

theorem hTens_tr {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α] [Fintype β]
    (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm, Finset.sum_congr rfl fun b _ => Finset.sum_comm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem piW_tmul (t : E →ₐ[F] Fv F v) (a : AF F) (x : E) : piW t (a ⊗ₜ[F] x) = evFin F v a * t x := rfl

theorem piW_smul (t : E →ₐ[F] Fv F v) (a : AF F) (z : AE F E) : piW t (a • z) = evFin F v a * piW t z := by
  rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply, piW_tmul, map_one, mul_one]
  rfl

theorem piW_inc (t : E →ₐ[F] Fv F v) (x : E) : piW t (inclR (F := F) (AF F) x) = t x :=
  (piW_tmul t 1 x).trans (by rw [map_one, one_mul])

theorem piW_cA (t : E →ₐ[F] Fv F v) (z : AE F E) : piW t (cA σ z) = piW (t.comp σ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

theorem trace_cm (h : IsCMExt F E σ) (x : E) : algebraMap F E (Algebra.trace F E x) = x + σ x := by
  classical
  have h1 := trace_eq_sum_embeddings (K := F) (L := E) (AlgebraicClosure E) (x := x)
  let τ : E →ₐ[F] AlgebraicClosure E := IsScalarTower.toAlgHom F E _
  have h2 : (Finset.univ : Finset (E →ₐ[F] AlgebraicClosure E)) = {τ, τ.comp σ} := by
    ext τ'
    simpa using eq_or_eq_comp_conj h τ τ'
  rw [h2, Finset.sum_pair (comp_conj_ne h τ).symm] at h1
  apply (algebraMap E (AlgebraicClosure E)).injective
  rw [← IsScalarTower.algebraMap_apply, h1, map_add]
  rfl

theorem trace_tmul {R : Type} [CommRing R] [Algebra F R] (r : R) (x : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] x) = r * algebraMap F R (Algebra.trace F E x) := by
  have h1 : (r ⊗ₜ[F] x : R ⊗[F] E) = r • ((1 : R) ⊗ₜ[F] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem ev_trace (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (z : AE F E) :
    evFin F v (Algebra.trace (AF F) (AE F E) z) = piW t z + piW (t.comp σ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero]
  | add x y hx hy => simp only [map_add, hx, hy]; ring
  | tmul a x =>
    rw [trace_tmul, map_mul, AlgHom.commutes, piW_tmul, piW_tmul, ← t.commutes, trace_cm h, map_add, mul_add]
    rfl

variable (v) in

def ep : AF F := atPlace v 1

theorem ep_mul (a : AF F) : ep v * a = atPlace v (evFin F v a) := by rw [ep, atPlace_mul_right, one_mul]

theorem ev_ep : evFin F v (ep v) = 1 := evFin_atPlace v 1

theorem ep_ep : ep v * ep v = ep v := by rw [ep_mul, ev_ep]; rfl

theorem off_eq (a : AF F) : off v a = (1 - ep v) * a := by rw [sub_mul, one_mul, ep_mul]; rfl

theorem ep_smul (z : AE F E) : ep v • z = tensAt E v (compFin F E v z) := by
  have := tensAt_mul_right (E := E) v 1 z
  rw [one_mul] at this
  rw [← this, Algebra.smul_def]
  rfl

theorem at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] (z : M) : At (evFin F v) z ↔ ep v • z = z := by
  constructor
  · intro h
    have := h (1 - ep v) (by rw [map_sub, map_one, ev_ep, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  · intro h a ha
    rw [← h, smul_smul, mul_comm, ep_mul, ha, map_zero, zero_smul]

theorem AE_ext (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {y z : AE F E} (h0 : (1 - ep v) • y = (1 - ep v) • z)
    (h1 : piW t y = piW t z) (h2 : piW (t.comp σ) y = piW (t.comp σ) z) : y = z := by
  have : ep v • y = ep v • z := by rw [ep_smul, ep_smul, split_ext h t h1 h2]
  rw [sub_smul, sub_smul, this, one_smul, one_smul] at h0
  exact sub_left_injective h0

theorem mat_ext (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {m n : Type} {y z : Matrix m n (AE F E)}
    (h0 : (1 - ep v) • y = (1 - ep v) • z) (h1 : y.map (piW t) = z.map (piW t))
    (h2 : y.map (piW (t.comp σ)) = z.map (piW (t.comp σ))) : y = z :=
  Matrix.ext fun i j => AE_ext h t (congrFun (congrFun h0 i) j) (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

def spM (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {m n : Type} (A B : Matrix m n (Fv F v)) : Matrix m n (AE F E) :=
  of fun i j => tensAt E v ((splitAlgEquiv h t).symm (A i j, B i j))

theorem spM_fst (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {m n : Type} (A B : Matrix m n (Fv F v)) :
    (spM h t A B).map (piW t) = A := Matrix.ext fun i j => by
  show splitProj t (compFin F E v (tensAt E v _)) = _
  rw [compFin_tensAt, splitProj_symm]

theorem spM_snd (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {m n : Type} (A B : Matrix m n (Fv F v)) :
    (spM h t A B).map (piW (t.comp σ)) = B := Matrix.ext fun i j => by
  show splitProj (t.comp σ) (compFin F E v (tensAt E v _)) = _
  rw [compFin_tensAt, splitProj_comp_symm]

theorem spM_off (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {m n : Type} (A B : Matrix m n (Fv F v)) :
    (1 - ep v) • spM h t A B = 0 := Matrix.ext fun i j => by
  show (1 - ep v) • tensAt E v _ = 0
  rw [sub_smul, one_smul, ep_smul, compFin_tensAt, sub_self]

theorem map_smul_piW (t : E →ₐ[F] Fv F v) {m n : Type} (a : AF F) (y : Matrix m n (AE F E)) :
    (a • y).map (piW t) = evFin F v a • y.map (piW t) := Matrix.ext fun _ _ => piW_smul t a _

theorem map_cA_piW (t : E →ₐ[F] Fv F v) {m n : Type} (y : Matrix m n (AE F E)) :
    (y.map (cA σ)).map (piW t) = y.map (piW (t.comp σ)) := Matrix.ext fun _ _ => piW_cA t _

theorem incM_piW (t : E →ₐ[F] Fv F v) {m n : Type} (J : Matrix m n E) : (incM F J).map (piW t) = J.map t :=
  Matrix.ext fun i j => by rw [map_apply, map_apply, incM, map_apply, piW_inc]

def mkM (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {n : ℕ} (A B : Matrix (Fin n) (Fin n) (Fv F v)) :
    Matrix (Fin n) (Fin n) (AE F E) := (1 - ep v) • 1 + spM h t A B

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def coB (σ : E →ₐ[F] E) (X : Spc F E n) (W : Spc F E d) (t : E →ₐ[F] Fv F v) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    Matrix (Fin n) (Fin d) (Fv F v) := -(X.J.map t * u.map (piW (t.comp σ)) * (W.J.map t)ᵀ)

theorem ev_symp (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (hX : ∀ i j, σ (X.J j i) = X.J i j)
    (hW : ∀ i j, σ (W.J j i) = -W.J i j) (w w' : Matrix (Fin n) (Fin d) (AE F E)) :
    evFin F v (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) w w') =
      trace (coB σ X W t w * (-w'.map (piW t))ᵀ) - trace (coB σ X W t w' * (-w.map (piW t))ᵀ) := by
  have a : ∀ t : E →ₐ[F] Fv F v, piW t (hTens (cA σ) (incM F X.J) (incM F W.J) w w') =
      trace ((w.map (piW t))ᵀ * X.J.map t * w'.map (piW (t.comp σ)) * (W.J.map t)ᵀ) := fun t => by
    rw [hTens_tr, AddMonoidHom.map_trace (piW t), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, transpose_map, transpose_map,
      incM_piW, incM_piW, map_cA_piW]
  have b1 : X.J.map (t.comp σ) = (X.J.map t)ᵀ := Matrix.ext fun i j => congrArg t (hX j i)
  have b2 : (W.J.map (t.comp σ))ᵀ = -W.J.map t := Matrix.ext fun i j => (congrArg t (hW i j)).trans (map_neg t _)
  rw [symp, ev_trace h t, map_mul, map_mul, a, a, comp_conj_conj h, b1, b2, coB, coB]
  generalize w.map (piW t) = A
  generalize w'.map (piW t) = A'
  generalize w.map (piW (t.comp σ)) = B
  generalize w'.map (piW (t.comp σ)) = B'
  generalize X.J.map t = P
  generalize W.J.map t = Q
  have c1 : trace (P * B * Qᵀ * A'ᵀ) = trace (Bᵀ * Pᵀ * A' * Q) := by
    rw [← trace_transpose, transpose_mul, transpose_mul, transpose_mul, transpose_transpose, transpose_transpose,
      ← Matrix.mul_assoc, trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have c2 : trace (P * B' * Qᵀ * Aᵀ) = trace (Aᵀ * P * B' * Qᵀ) := by
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  simp only [transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, c1, c2, map_neg, map_one, trace_neg]
  ring

end Split

section Gen
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {v : HeightOneSpectrum (𝓞 F)}

theorem cont_at : Continuous (atPlace (F := F) v) := continuous_const.prodMk (continuous_singleFin v)

theorem cont_evI : Continuous (evI F) :=
  (continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
    ((continuous_apply w.1).comp continuous_fst)).prodMk
  (continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp
    ((continuous_apply w.1).comp continuous_fst))

theorem cont_mixS : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

open scoped Classical in
theorem pure_cont (f : SInf F κ) {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : Good φ) :
    Continuous (pure f φ) :=
  (f.continuous.comp (continuous_pi fun i => cont_evI.comp (continuous_apply i))).mul
    ((pf_mem hφ).1.continuous.comp (continuous_pi fun i => continuous_snd.comp (continuous_apply i)))

open scoped Classical in
theorem pure_cs (f : SInf F κ) (hf : HasCompactSupport f) {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ}
    (hφ : Good φ) : HasCompactSupport (pure f φ) := by
  let j : (κ → mixedEmbedding.mixedSpace F) × (κ → Af F) → κ → AF F := fun p i =>
    pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i)) (p.2 i)
  have hj : Continuous j := continuous_pi fun i =>
    (cont_mixS.comp ((continuous_apply i).comp continuous_fst)).prodMk
      ((continuous_apply i).comp continuous_snd)
  refine HasCompactSupport.intro ((hf.isCompact.prod (pf_mem hφ).2.isCompact).image hj) fun x hx => ?_
  by_contra h0
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h0
  refine hx ⟨(_, fun i => sndA F (x i)), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, funext fun i => ?_⟩
  exact Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _) rfl

open Classical in
theorem exists_bump : ∃ f : SInf F κ, HasCompactSupport f ∧ f 0 = 1 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport fun x => (b x : ℂ) := b.hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), h1, ?_⟩
  show (b 0 : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one), Complex.ofReal_one]

open Classical in
theorem rest_zero {f : SInf F κ} (hf : f 0 = 1) : pure f (Function.update (stdF κ) v 1) 0 = 1 := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  rw [finprod_eq_one_of_forall_eq_one, mul_one, ← hf]
  · congr 1
    funext i
    exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  · intro u
    by_cases h : u = v
    · subst h; simp
    · rw [Function.update_of_ne h, stdF, Set.indicator_of_mem (fun i => by simp)]; rfl

theorem tens_at {r : (κ → AF F) → ℂ} (h : Indep v r) (φ : (κ → Fv F v) → ℂ) (t : κ → Fv F v) :
    tens (evFin F v) φ r (fun i => atPlace v (t i)) = φ t * r 0 := by
  rw [tens, ← h 0 t, zero_add]
  simp only [evFin_atPlace]

def sub {n d : ℕ} {k : Type} [Field k] (γ : GL (Fin n) k) : Module.End ℂ (Matrix (Fin n) (Fin d) k → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun Y => γ.1 * Y

theorem sub_mem {n d : ℕ} (γ : GL (Fin n) (Fv F v)) {f : Matrix (Fin n) (Fin d) (Fv F v) → ℂ} (hf : f ∈ SB _) :
    sub γ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)) := by
  let h : Matrix (Fin n) (Fin d) (Fv F v) ≃ₜ Matrix (Fin n) (Fin d) (Fv F v) :=
    { toFun := fun Y => γ.1 * Y
      invFun := fun Y => (γ⁻¹).1 * Y
      left_inv := fun Y => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun Y => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      continuous_toFun := continuous_const.matrix_mul continuous_id
      continuous_invFun := continuous_const.matrix_mul continuous_id }
  exact ⟨hf.1.comp_continuous h.continuous, hf.2.comp_homeomorph h⟩

theorem int_sq {X : Type} [MeasurableSpace X] (μ : Measure X) {f : X → ℂ} (hf : AEStronglyMeasurable f μ) :
    ∫ x, f x * (starRingEnd ℂ) (f x) ∂μ = ((∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ).toReal : ℝ) := by
  simp only [Complex.mul_conj']
  rw [← show ∫ x, ‖f x‖ ^ 2 ∂μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ).toReal from ?_, ← integral_complex_ofReal]
  · simp
  · rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖f x‖ ^ 2) (.of_forall fun x => sq_nonneg _) (hf.norm.pow 2)]
    congr 2
    funext x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

set_option maxHeartbeats 1600000 in
theorem gen [IsTotallyReal F] (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) {n d : ℕ}
    (hnd : 2 * n < d + 2)
    (e : (Matrix (Fin n) (Fin d) (Fv F v) × Matrix (Fin n) (Fin d) (Fv F v)) ≃ₗ[Fv F v]
      (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))
    (he : ∀ w w', (e w).1 ⬝ᵥ (e w').2 - (e w').1 ⬝ᵥ (e w).2 = trace (w.1 * w'.2ᵀ) - trace (w'.1 * w.2ᵀ))
    (O : GL (Fin n) (Fv F v) → Module.End ℂ ((Fin n × Fin d → AF F) → ℂ))
    (hmul : ∀ γ γ', O (γ * γ') = O γ' * O γ) (hone : O 1 = 1)
    (pres : ∀ γ, ∀ Φ ∈ schA F (Fin n × Fin d), O γ Φ ∈ schA F (Fin n × Fin d))
    (adm : ∀ γ, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ O γ ∈ (adeleClass F).adm (Fin n × Fin d))
    (unit : ∀ μ : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ γ, ∀ φ ∈ schA F (Fin n × Fin d), ∫⁻ x, ‖O γ φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ)
    (impl : ∀ γ w, ∃ w', (∀ Φ ∈ schA F (Fin n × Fin d), O γ (schr ψ w Φ) = schr ψ w' (O γ Φ)) ∧ offP v w' = offP v w ∧
      ∀ Y Z, evP v w = e (Y, Z) → evP v w' = e ((γ⁻¹).1 * Y, γ.1ᵀ * Z)) :
    ∃ I : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ),
      Set.BijOn I (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _) ∧
      (∀ φ ∈ SB _, ∀ Y₀ Y, I (schr (psv v ψ) (e (Y₀, 0)) φ) Y = I φ (Y + Y₀)) ∧
      (∀ φ ∈ SB _, ∀ Z Y, I (schr (psv v ψ) (e (0, Z)) φ) Y = psv v ψ (trace (Y * Zᵀ)) * I φ Y) ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), ∃ z : GL (Fin n) (Fv F v) →₀ ℂ, (z.sum fun _ a => a) ≠ 0 ∧
        (z.sum fun γ a => a • O γ Φ) ∈ Submodule.span ℂ {Ψ | ∃ f φ, Good φ ∧
          (∀ Y : Matrix (Fin n) (Fin d) (Fv F v), Y.rank ≠ n → I (φ v) Y = 0) ∧ Ψ = pure f φ} := by
  classical
  have hc : Continuous (psv v ψ) := hψ.1.comp cont_at
  have h1 : psv v ψ ≠ 1 := fun h => by
    obtain ⟨y, hy⟩ := (GlobalTheory.T.localComponents_nontrivial_adelic_character F ψ hψ).1 v
    exact hy (DFunLike.congr_fun h y)
  obtain ⟨I, J, hI, hJ, htr, hmod⟩ := svn (psv v ψ) hc h1 e he
  have inj : ∀ φ ∈ SB _, ∀ φ' ∈ SB _, I φ = I φ' → φ = φ' := fun φ h φ' h' e => by
    rw [← (hI φ h).2, e, (hI φ' h').2]
  refine ⟨I, ⟨fun φ h => (hI φ h).1, inj, fun f hf => ⟨J f, (hJ f hf).1, (hJ f hf).2⟩⟩, htr, hmod, ?_⟩
  have hfull : ∀ φ ∈ SB _, ∀ Y₀ Z Y, I (schr (psv v ψ) (e (Y₀, Z)) φ) Y =
      psv v ψ (-(⅟2 * trace (Y₀ * Zᵀ))) * (psv v ψ (trace ((Y + Y₀) * Zᵀ)) * I φ (Y + Y₀)) := fun φ hφ Y₀ Z Y => by
    have := congrArg (fun f => I f Y) (schr_schr (psv v ψ) (e (Y₀, 0)) (e (0, Z)) φ)
    simp only [he, ← map_add, Prod.mk_add_mk, add_zero, zero_add, map_smul, Pi.smul_apply, smul_eq_mul, Matrix.zero_mul,
      trace_zero, sub_zero] at this
    rw [htr _ (schr_mem_SB hc _ hφ), hmod _ hφ] at this
    rw [this, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  let S : GL (Fin n) (Fv F v) → Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ) := fun γ => J ∘ₗ sub γ ∘ₗ I
  have hS : ∀ γ, ∀ φ ∈ SB _, S γ φ ∈ SB _ := fun γ φ h => (hJ _ (sub_mem γ (hI φ h).1)).1
  have IS : ∀ γ, ∀ φ ∈ SB _, ∀ Y, I (S γ φ) Y = I φ (γ.1 * Y) := fun γ φ h Y =>
    congrFun (hJ _ (sub_mem γ (hI φ h).1)).2 Y
  have SS : ∀ γ γ', ∀ φ ∈ SB _, S γ (S γ' φ) = S (γ' * γ) φ := fun γ γ' φ h =>
    inj _ (hS _ _ (hS _ _ h)) _ (hS _ _ h) (funext fun Y => by
      rw [IS _ _ (hS _ _ h), IS _ _ h, IS _ _ h, Units.val_mul, Matrix.mul_assoc])
  have S1 : ∀ φ ∈ SB _, S 1 φ = φ := fun φ h => inj _ (hS _ _ h) _ h (funext fun Y => by
    rw [IS _ _ h, Units.val_one, Matrix.one_mul])
  have Scomm : ∀ γ, ∀ φ ∈ SB _, ∀ Y₀ Z, S γ (schr (psv v ψ) (e (γ.1 * Y₀, (γ⁻¹).1ᵀ * Z)) φ) =
      schr (psv v ψ) (e (Y₀, Z)) (S γ φ) := fun γ φ h Y₀ Z =>
    inj _ (hS _ _ (schr_mem_SB hc _ h)) _ (schr_mem_SB hc _ (hS _ _ h)) (funext fun Y => by
      have t : ∀ A : Matrix (Fin n) (Fin d) (Fv F v), trace (γ.1 * A * ((γ⁻¹).1ᵀ * Z)ᵀ) = trace (A * Zᵀ) := fun A => by
        rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_assoc,
          Units.inv_mul, Matrix.mul_one]
      rw [IS _ _ (schr_mem_SB hc _ h), hfull _ h, hfull _ (hS _ _ h), IS _ _ h, ← Matrix.mul_add, t, t])
  have key : ∀ γ, ∃ a : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), O γ Φ = a • lift v (S γ) Φ := fun γ => by
    obtain ⟨a, ha⟩ := schur F ψ hψ hstd (lift v (S γ⁻¹) * O γ) (fun l hl => adm γ _ (lift_adm (hS _) l hl))
      fun w Φ hΦ => by
        obtain ⟨w', h1, h2, h3⟩ := impl γ w
        obtain ⟨⟨Y, Z⟩, hYZ⟩ := e.surjective (evP v w)
        rw [Module.End.mul_apply, Module.End.mul_apply, h1 Φ hΦ]
        refine lift_schr ψ h2 (fun φ hφ => ?_) (pres γ Φ hΦ)
        rw [h3 Y Z hYZ.symm, ← hYZ, ← Scomm γ⁻¹ φ hφ, inv_inv]
    refine ⟨a, fun Φ hΦ => ?_⟩
    rw [← map_smul, ← ha Φ hΦ, Module.End.mul_apply,
      lift_lift (S'' := 1) (hS _) (fun φ h => by rw [SS _ _ _ h, inv_mul_cancel, S1 _ h]; rfl) (pres γ Φ hΦ), lift_one]
  choose χ₀ hχ using key
  obtain ⟨f₀, hf₀, hf0⟩ := exists_bump (F := F) (κ := Fin n × Fin d)
  let r := pure f₀ (Function.update (stdF (Fin n × Fin d)) v 1)
  have hr : Indep v r := indep_pure _ _
  let Ψ : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) → (Fin n × Fin d → AF F) → ℂ := fun f => tens (evFin F v) (J f) r
  have hΨ : ∀ f, Ψ f = pure f₀ (Function.update (stdF (Fin n × Fin d)) v (J f)) := fun f =>
    (pure_update f₀ good_std.2 _).symm
  have Ψm : ∀ f ∈ SB _, Ψ f ∈ schA F _ := fun f hf => hΨ f ▸ pure_mem _ (good_std.update (hJ f hf).1)
  have Ψc : ∀ f ∈ SB _, Continuous (Ψ f) := fun f hf => hΨ f ▸ pure_cont _ (good_std.update (hJ f hf).1)
  have Ψs : ∀ f ∈ SB _, HasCompactSupport (Ψ f) := fun f hf => hΨ f ▸ pure_cs _ hf₀ (good_std.update (hJ f hf).1)
  have Ψ0 : ∀ f ∈ SB _, Ψ f = 0 → f = 0 := fun f hf h => by
    have : J f = 0 := funext fun t => by
      have : tens (evFin F v) (J f) r (fun i => atPlace v (t i)) = 0 := congrFun h _
      rwa [tens_at hr, show r 0 = 1 from rest_zero hf0, mul_one] at this
    rw [← (hJ f hf).2, this, map_zero]
  have Ψa : ∀ f g, Ψ (f + g) = Ψ f + Ψ g := fun f g => funext fun x => by simp only [Ψ, tens, map_add, Pi.add_apply, add_mul]
  have Ψsm : ∀ (c : ℂ) f, Ψ (c • f) = c • Ψ f := fun c f => funext fun x => by
    simp only [Ψ, tens, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have ΨO : ∀ γ, ∀ f ∈ SB _, O γ (Ψ f) = χ₀ γ • Ψ (sub γ f) := fun γ f hf => by
    rw [hχ γ _ (Ψm f hf), lift_tens _ _ hr]
    show _ • tens _ (J (sub γ (I (J f)))) r = _
    rw [(hJ f hf).2]
  have hf₁ := (hI _ (stdF_mem (κ := Fin n × Fin d) v)).1
  have hne : ∀ γ, Ψ (sub γ (I (stdF _ v))) ≠ 0 := fun γ h => by
    have h2 := Ψ0 _ (sub_mem γ hf₁) h
    have h3 : I (stdF _ v) = 0 := funext fun Y => by
      have := congrFun h2 ((γ⁻¹).1 * Y)
      rwa [sub, LinearMap.funLeft_apply, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at this
    have h4 := congrFun (inj _ (stdF_mem v) 0 (zero_mem _) (by rw [h3, map_zero])) 0
    rw [stdF, Set.indicator_of_mem (by exact fun i => zero_mem _)] at h4
    exact one_ne_zero h4
  let χ : GL (Fin n) (Fv F v) →* ℂ :=
    { toFun := χ₀
      map_one' := by
        have := ΨO 1 _ hf₁
        rw [hone, Module.End.one_apply] at this
        have e1 : sub 1 (I (stdF _ v)) = I (stdF _ v) := funext fun Y => congrArg (I (stdF _ v)) (Matrix.one_mul Y)
        refine smul_left_injective ℂ (hne 1) ?_
        simp only
        rw [← this, one_smul, e1]
      map_mul' := fun γ γ' => by
        have := ΨO (γ * γ') _ hf₁
        rw [hmul, Module.End.mul_apply, ΨO γ _ hf₁, map_smul, ΨO γ' _ (sub_mem γ hf₁), smul_smul] at this
        have e1 : sub γ' (sub γ (I (stdF _ v))) = sub (γ * γ') (I (stdF _ v)) :=
          funext fun Y => congrArg (I (stdF _ v)) (Matrix.mul_assoc _ _ Y).symm
        rw [e1] at this
        exact (smul_left_injective ℂ (hne _) this).symm }
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  have hint : ∀ f g : SB (Matrix (Fin n) (Fin d) (Fv F v)), Integrable (fun x => Ψ f x * (starRingEnd ℂ) (Ψ g x)) μ :=
    fun f g => ((Ψc _ f.2).mul (Complex.continuous_conj.comp (Ψc _ g.2))).integrable_of_hasCompactSupport
      (Ψs _ f.2).mul_right
  let B : SB (Matrix (Fin n) (Fin d) (Fv F v)) →ₗ[ℂ] SB (Matrix (Fin n) (Fin d) (Fv F v)) →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun f g => ∫ x, Ψ f x * (starRingEnd ℂ) (Ψ g x) ∂μ)
      (fun f f' g => by
        rw [← integral_add (hint _ _) (hint _ _)]
        simp only [Submodule.coe_add, Ψa, Pi.add_apply, add_mul])
      (fun c f g => by
        simp only [Submodule.coe_smul, Ψsm, Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply, integral_const_mul])
      (fun f g g' => by
        rw [← integral_add (hint _ _) (hint _ _)]
        simp only [Submodule.coe_add, Ψa, Pi.add_apply, map_add, mul_add])
      (fun c f g => by
        simp only [Submodule.coe_smul, Ψsm, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm _ ((starRingEnd ℂ) c),
          integral_const_mul])
  have Binv : ∀ (p : Matrix (Fin n) (Fin d) (Fv F v) × Matrix (Fin n) (Fin d) (Fv F v))
      (f f' g g' : SB (Matrix (Fin n) (Fin d) (Fv F v))), f'.1 = I (schr (psv v ψ) (e p) (J f)) →
      g'.1 = I (schr (psv v ψ) (e p) (J g)) → B f' g' = B f g := fun p f f' g g' hf hg => by
    let w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) := (fun i => atPlace v ((e p).1 i), fun i => atPlace v ((e p).2 i))
    have k : ∀ f f' : SB (Matrix (Fin n) (Fin d) (Fv F v)), f'.1 = I (schr (psv v ψ) (e p) (J f)) →
        Ψ f' = schr ψ w (Ψ f) := fun f f' hf => by
      rw [schr_tens ψ w _ hr, show offP v w = 0 from Prod.ext (funext fun i => off_at v _) (funext fun i => off_at v _),
        schr_zero, show evP v w = e p from Prod.ext (funext fun i => evFin_atPlace v _) (funext fun i => evFin_atPlace v _),
        hf]
      simp only [Ψ]
      rw [(hI _ (schr_mem_SB hc _ (hJ _ f.2).1)).2]
    show ∫ x, Ψ f' x * (starRingEnd ℂ) (Ψ g' x) ∂μ = ∫ x, Ψ f x * (starRingEnd ℂ) (Ψ g x) ∂μ
    rw [k f f' hf, k g g' hg, ← integral_add_right_eq_self (fun x => Ψ f x * (starRingEnd ℂ) (Ψ g x)) w.1]
    congr 1
    funext x
    simp only [schr, map_mul]
    rw [mul_mul_mul_comm, Complex.mul_conj', hψ.2.1]
    simp
  intro Φ hΦ
  obtain ⟨m, c, g, rfl⟩ := Submodule.mem_span_set'.1 (schA_le hΦ)
  choose f φ hφ hg using fun i => (g i).2
  obtain ⟨z, hz, hz'⟩ := comb (psv v ψ) hc h1 hnd χ B
    (fun Y₀ f f' g g' hf hg => Binv (Y₀, 0) f f' g g'
      (funext fun Y => by rw [htr _ (hJ _ f.2).1, (hJ _ f.2).2, hf])
      (funext fun Y => by rw [htr _ (hJ _ g.2).1, (hJ _ g.2).2, hg]))
    (fun Z f f' g g' hf hg => Binv (0, Z) f f' g g'
      (funext fun Y => by rw [hmod _ (hJ _ f.2).1, (hJ _ f.2).2, hf])
      (funext fun Y => by rw [hmod _ (hJ _ g.2).1, (hJ _ g.2).2, hg]))
    (fun x => hψ.2.1 _)
    (fun f hf h0 => by
      have h2 : ∫ x, Ψ f x * (starRingEnd ℂ) (Ψ f x) ∂μ = 0 := h0
      simp only [Complex.mul_conj', ← Complex.ofReal_pow, integral_complex_ofReal, Complex.ofReal_eq_zero] at h2
      obtain ⟨x, hx⟩ := Function.ne_iff.1 fun h => hf (Subtype.ext (Ψ0 _ f.2 h))
      exact (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (f := fun x => ‖Ψ f x‖ ^ 2)
        ((Ψc _ f.2).norm.pow 2) ((Ψs _ f.2).comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)) (fun x => by positivity)
        (x := x) (pow_ne_zero 2 (norm_ne_zero_iff.2 hx))).ne' h2)
    (fun γ f f' hf => by
      have e1 : Ψ f' = O γ (Ψ f) := by
        rw [ΨO γ _ f.2, ← Ψsm]
        exact congrArg Ψ (funext hf)
      show ∫ x, Ψ f' x * (starRingEnd ℂ) (Ψ f' x) ∂μ = ∫ x, Ψ f x * (starRingEnd ℂ) (Ψ f x) ∂μ
      rw [int_sq μ ((Ψc _ f'.2).stronglyMeasurable_of_hasCompactSupport (Ψs _ f'.2)).aestronglyMeasurable,
        int_sq μ ((Ψc _ f.2).stronglyMeasurable_of_hasCompactSupport (Ψs _ f.2)).aestronglyMeasurable, e1,
        unit μ inferInstance γ _ (Ψm _ f.2)])
    (Finset.univ.image fun i => I (φ i v)) (fun f hf => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hf
      exact (hI _ ((hφ i).1 v)).1)
  refine ⟨z, hz, ?_⟩
  let Sz : Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ) := z.sum fun γ a => (a * χ₀ γ) • S γ
  have e1 : (z.sum fun γ a => a • O γ (∑ i, c i • (g i).1)) = lift v Sz (∑ i, c i • (g i).1) := by
    generalize (∑ i, c i • (g i).1) = Φ at hΦ
    funext x
    simp only [Finsupp.sum, hχ _ _ hΦ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, lift_apply]
    simp only [Sz, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      mul_assoc]
  rw [e1, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul, hg, lift_pure _ _ (hφ i)]
  have hv := (hφ i).1 v
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, (hφ i).update ?_, fun Y hY => ?_, rfl⟩)
  · simp only [Sz, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun γ _ => Submodule.smul_mem _ _ (hS _ _ hv)
  · rw [Function.update_self, ← hz' _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)) Y hY]
    simp only [Sz, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, IS _ _ hv, mul_assoc]
    rfl

end Gen

section PartB
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE cA incM UA Spc Model Rep mat HasSig)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem offP_eq {κ : Type} (w : (κ → AF F) × (κ → AF F)) : offP v w = (1 - ep v) • w :=
  Prod.ext (funext fun _ => off_eq _) (funext fun _ => off_eq _)

theorem evalEmbedding_smul {κ : Type} (a : AF F) (w : (κ → AF F) × (κ → AF F)) : evP v (a • w) = evFin F v a • evP v w :=
  Prod.ext (funext fun _ => map_mul (evFin F v) _ _) (funext fun _ => map_mul (evFin F v) _ _)

theorem evalPoints_add {κ : Type} (w w' : (κ → AF F) × (κ → AF F)) : evP v (w + w') = evP v w + evP v w' :=
  Prod.ext (funext fun _ => map_add (evFin F v) _ _) (funext fun _ => map_add (evFin F v) _ _)

end PartB

section PartA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.MainNotions.StandardLattice GlobalTheory.ChiGrid GlobalTheory.FunObj
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (skewGram mulG colV adjV₁ incM boxB IsDatumB)
open Formalism.IndefR.Datum.Brg (GG GI cA_inc GG_herm GI_GG)
open scoped ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure IsTh {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (G : (κ → AF F) × (κ → AF F) → ℂ) : Prop where
  hq : ∀ (ξ η : κ → F) (w : (κ → AF F) × (κ → AF F)),
      G ((fun i => algebraMap F (AF F) (ξ i), fun i => algebraMap F (AF F) (η i)) + w) =
        ψ (-(⅟(2 : AF F) * ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ w.2 - w.1 ⬝ᵥ fun i => algebraMap F (AF F) (η i)))) * G w
  hl : ∃ U : AddSubgroup ((κ → AF F) × (κ → AF F)), IsOpen (U : Set ((κ → AF F) × (κ → AF F))) ∧
      ∀ u ∈ U, (∀ i, fstA F (u.1 i) = 0 ∧ fstA F (u.2 i) = 0) →
        ∀ w : (κ → AF F) × (κ → AF F), ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ u.2 - u.1 ⬝ᵥ w.2)) * G (w + u) = G w
  hc : Continuous G
  hs : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ (κ → AF F) × (κ → AF F)), Continuous L →
      (∀ t i, sndA F ((L t).1 i) = 0 ∧ sndA F ((L t).2 i) = 0) → ∀ w, ContDiff ℝ ∞ fun t => G (w + L t)

theorem IsTh.zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) :
    IsTh ψ (fun _ : (κ → AF F) × (κ → AF F) => 0) :=
  ⟨fun _ _ _ => (mul_zero _).symm, ⟨⊤, isOpen_univ, fun _ _ _ _ => mul_zero _⟩, continuous_const,
    fun _ _ _ _ _ => contDiff_const⟩

theorem IsTh.add {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}
    {G H : (κ → AF F) × (κ → AF F) → ℂ} (hG : IsTh ψ G) (hH : IsTh ψ H) : IsTh ψ fun w => G w + H w := by
  obtain ⟨U, hU, h1⟩ := hG.hl
  obtain ⟨U', hU', h2⟩ := hH.hl
  exact ⟨fun ξ η w => by rw [hG.hq, hH.hq, mul_add], ⟨U ⊓ U', hU.inter hU', fun u hu h0 w => by
    rw [mul_add, h1 u hu.1 h0, h2 u hu.2 h0]⟩, hG.hc.add hH.hc, fun k L a b w => (hG.hs k L a b w).add (hH.hs k L a b w)⟩

theorem IsTh.smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}
    {G : (κ → AF F) × (κ → AF F) → ℂ} (hG : IsTh ψ G) (c : ℂ) : IsTh ψ fun w => c * G w := by
  obtain ⟨U, hU, h1⟩ := hG.hl
  exact ⟨fun ξ η w => by rw [hG.hq, mul_left_comm], ⟨U, hU, fun u hu h0 w => by
    rw [mul_left_comm, h1 u hu h0]⟩, continuous_const.mul hG.hc, fun k L a b w => contDiff_const.mul (hG.hs k L a b w)⟩

theorem IsTh.sum {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} {ι : Type}
    (s : Finset ι) {G : ι → (κ → AF F) × (κ → AF F) → ℂ} (hG : ∀ i ∈ s, IsTh ψ (G i)) : IsTh ψ fun w => ∑ i ∈ s, G i w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsTh.zero ψ
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hG a (Finset.mem_insert_self _ _)).add (ih fun i hi => hG i (Finset.mem_insert_of_mem hi))

variable {D : D7}

def lA (M V V₂ : HSp D) {d : ℕ} (e : Fin V.rank ⊕ Fin V₂.rank ≃ Fin d) :
    Matrix (Fin M.rank) (Fin d) (AE D) →ₗ[AF D.host.F] WO M V where
  toFun u := mulG M (u.submatrix id fun k => e (.inl k))ᵀ
  map_add' u u' := Matrix.add_mul (u.submatrix id fun k => e (.inl k))ᵀ (u'.submatrix id fun k => e (.inl k))ᵀ (GG M)
  map_smul' a u := Matrix.smul_mul a (u.submatrix id fun k => e (.inl k))ᵀ (GG M)

def lB (M V V₂ : HSp D) {d : ℕ} (e : Fin V.rank ⊕ Fin V₂.rank ≃ Fin d) :
    Matrix (Fin M.rank) (Fin d) (AE D) →ₗ[AF D.host.F] WO (negSp V₂) M where
  toFun u := -mulG V₂ ((u.submatrix id fun k => e (.inr k)).map (cA D))
  map_add' u u' := by
    have : ((u + u').submatrix id fun k => e (.inr k)).map (cA D) =
        (u.submatrix id fun k => e (.inr k)).map (cA D) + (u'.submatrix id fun k => e (.inr k)).map (cA D) :=
      Matrix.ext fun _ _ => map_add (cA D) _ _
    rw [this, ← neg_add]
    exact congrArg Neg.neg (Matrix.add_mul _ _ (GG V₂))
  map_smul' a u := by
    have : ((a • u).submatrix id fun k => e (.inr k)).map (cA D) = a • (u.submatrix id fun k => e (.inr k)).map (cA D) :=
      Matrix.ext fun _ _ => map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) _ _
    rw [this, RingHom.id_apply, smul_neg]
    exact congrArg Neg.neg (Matrix.smul_mul a _ (GG V₂))

end PartA

section Datum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.MainNotions.StandardLattice GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.StdFrames
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (boxB IsDatumB)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Datum

end PositivityTheory.Member.ZakTransform
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
