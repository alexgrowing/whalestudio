import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelConj

set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology NumberField.mixedEmbedding
open scoped NumberField.AdeleRing SchwartzMap ContDiff Classical nonZeroDivisors

namespace GlobalTheory.CompanionTheory.RgEisTestSph

open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix PositivityTheory.RgEis

variable {k : Type} [Field k] [NumberField k]

def q₀ (u : mixedSpace k) : ℝ := ∑ w : InfinitePlace k, normAtPlace w u ^ 2

def qI {ι : Type} [Fintype ι] (u : ι → mixedSpace k) : ℝ := ∑ i, q₀ (u i)

theorem contDiff_normAtPlace_sq (w : InfinitePlace k) :
    ContDiff ℝ (∞) fun u : mixedSpace k => normAtPlace w u ^ 2 := by
  by_cases hw : w.IsReal
  · have h : (fun u : mixedSpace k => normAtPlace w u ^ 2) = fun u => ‖u.1 ⟨w, hw⟩‖ ^ 2 := by
      funext u
      rw [normAtPlace_apply_of_isReal hw]
    rw [h]
    exact (contDiff_norm_sq ℝ).comp
      ((contDiff_apply ℝ ℝ (⟨w, hw⟩ : {w : InfinitePlace k // w.IsReal})).comp contDiff_fst)
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    have h : (fun u : mixedSpace k => normAtPlace w u ^ 2) = fun u => ‖u.2 ⟨w, hc⟩‖ ^ 2 := by
      funext u
      rw [normAtPlace_apply_of_isComplex hc]
    rw [h]
    exact (contDiff_norm_sq ℝ).comp
      ((contDiff_apply ℝ ℂ (⟨w, hc⟩ : {w : InfinitePlace k // w.IsComplex})).comp contDiff_snd)

theorem contDiff_q₀ : ContDiff ℝ (∞) (q₀ (k := k)) := by
  unfold q₀
  exact ContDiff.sum (f := fun w u => normAtPlace w u ^ 2) (s := Finset.univ)
    fun w _ => contDiff_normAtPlace_sq w

theorem contDiff_qI {ι : Type} [Fintype ι] : ContDiff ℝ (∞) (qI (k := k) (ι := ι)) := by
  unfold qI
  apply ContDiff.sum
  intro i _
  have hi : ContDiff ℝ (∞) fun u : ι → mixedSpace k => u i := contDiff_apply ℝ (mixedSpace k) i
  exact (contDiff_q₀ (k := k)).comp hi

theorem q₀_nonneg (u : mixedSpace k) : 0 ≤ q₀ u := by
  unfold q₀
  exact Finset.sum_nonneg fun w _ => sq_nonneg _

theorem norm_le_sqrt_q₀ (u : mixedSpace k) : ‖u‖ ≤ Real.sqrt (q₀ u) := by
  rw [norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  unfold q₀
  exact Finset.single_le_sum (f := fun w => normAtPlace w u ^ 2) (fun w _ => sq_nonneg _)
    (Finset.mem_univ w)

theorem isBounded_q₀ (c : ℝ) : Bornology.IsBounded {u : mixedSpace k | q₀ u ≤ c} := by
  refine (Metric.isBounded_closedBall (x := (0 : mixedSpace k)) (r := Real.sqrt c)).subset ?_
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_sqrt_q₀ u).trans (Real.sqrt_le_sqrt hu)

theorem isBounded_qI {ι : Type} [Fintype ι] (c : ℝ) :
    Bornology.IsBounded {u : ι → mixedSpace k | qI u ≤ c} := by
  refine (Metric.isBounded_closedBall (x := (0 : ι → mixedSpace k)) (r := Real.sqrt c)).subset ?_
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg c)]
  intro i
  refine (norm_le_sqrt_q₀ (u i)).trans (Real.sqrt_le_sqrt ?_)
  have hu' : qI u ≤ c := hu
  unfold qI at hu'
  exact le_trans (Finset.single_le_sum (f := fun i => q₀ (u i)) (fun i _ => q₀_nonneg (u i))
    (Finset.mem_univ i)) hu'

theorem exists_bump {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (q : E → ℝ) (hq : ContDiff ℝ (∞) q) (hb : ∀ c, Bornology.IsBounded {x | q x ≤ c}) (c : ℝ) :
    ∃ f : 𝓢(E, ℂ), ∀ x, f x = (Real.smoothTransition (c - q x) : ℂ) := by
  have hf : ContDiff ℝ (∞) (fun x => ((Real.smoothTransition (c - q x) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (contDiff_const.sub hq))
  have hs : HasCompactSupport (fun x => ((Real.smoothTransition (c - q x) : ℝ) : ℂ)) := by
    refine HasCompactSupport.intro (hb c).isCompact_closure fun x hx => ?_
    have hx' : c < q x := by
      by_contra hle
      exact hx (subset_closure (not_lt.mp hle))
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), Complex.ofReal_zero]
  exact ⟨hs.toSchwartzMap hf, fun x => rfl⟩

def IntF (y : 𝔸ᶠ[k]) : Prop := ∀ v : HeightOneSpectrum (𝓞 k), y v ∈ v.adicCompletionIntegers k

theorem mem_one_iff (y : 𝔸ᶠ[k]) : y ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) ↔ IntF y := by
  change (∀ v : HeightOneSpectrum (𝓞 k), Valued.v (y v) ≤
      WithZero.exp (-FractionalIdeal.count k v ((1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) :
        FractionalIdeal (𝓞 k)⁰ k))) ↔ IntF y
  simp only [Units.val_one, FractionalIdeal.count_one, neg_zero, WithZero.exp_zero, IntF,
    HeightOneSpectrum.mem_adicCompletionIntegers]

open Classical in
theorem ind_apply (y : 𝔸ᶠ[k]) :
    cosetIndicator (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 0 y = if IntF y then 1 else 0 := by
  delta GroundTheory.Global.cosetIndicator
  simp only [Set.indicator_apply, Set.mem_vadd_set, vadd_eq_add, zero_add, exists_eq_right,
    SetLike.mem_coe, mem_one_iff, Pi.one_apply]
  all_goals (by_cases h : IntF y <;> simp [h])

theorem mem_intAd_iff (a : 𝔸[k]) : a ∈ intAd k ↔ IntF a.2 := by
  exact Subring.mem_iInf.trans (forall_congr' fun v => Iff.rfl)

theorem intF_line {ι : Type} [Fintype ι] (v m : ι → 𝔸[k]) (hv : ∀ i, v i ∈ intAd k)
    (hm : ∀ i, m i ∈ intAd k) (h1 : ∑ i, m i * v i = 1) (t : 𝔸[k]) :
    (∀ i, IntF ((t * v i).2)) ↔ IntF t.2 := by
  constructor
  · intro h
    have ht : t = ∑ i, m i * (t * v i) := by
      rw [show ∑ i, m i * (t * v i) = t * ∑ i, m i * v i by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring, h1, mul_one]
    have htm : t ∈ intAd k := by
      rw [ht]
      exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hm i) ((mem_intAd_iff _).mpr (h i))
    exact (mem_intAd_iff t).mp htm
  · intro h i
    exact (mem_intAd_iff _).mp (Subring.mul_mem _ ((mem_intAd_iff t).mpr h) (hv i))

theorem q₀_inf (a : 𝔸[k]) : q₀ (homeomorphMixedSpace k a.1) =
    ∑ w : InfinitePlace k, ‖(adStd k).φ w a‖ ^ 2 := by
  unfold q₀
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [GroundTheory.Global.normAtPlace_homeomorphMixedSpace]
  show ‖a.1 w‖ ^ 2 = ‖(InfinitePlace.Completion.extensionEmbedding w) (a.1 w)‖ ^ 2
  rw [(InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]

theorem qI_line {ι : Type} [Fintype ι] (v : ι → 𝔸[k])
    (hv : ∀ w, ∑ i, ‖(adStd k).φ w (v i)‖ ^ 2 = 1) (t : 𝔸[k]) :
    qI (infPartPi (t • v)) = q₀ (homeomorphMixedSpace k t.1) := by
  unfold qI
  have e1 : ∀ i, q₀ (infPartPi (t • v) i) =
      ∑ w : InfinitePlace k, ‖(adStd k).φ w t‖ ^ 2 * ‖(adStd k).φ w (v i)‖ ^ 2 := by
    intro i
    rw [show infPartPi (t • v) i = homeomorphMixedSpace k (t * v i).1 from rfl, q₀_inf]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_mul, norm_mul, mul_pow]
  simp only [e1]
  rw [Finset.sum_comm, q₀_inf]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.mul_sum, hv w, mul_one]

theorem col_norm {ι : Type} [Fintype ι] [DecidableEq ι] (κ : (adStd k).kGL ι) (i₀ : ι)
    (w : InfinitePlace k) :
    ∑ i, ‖(adStd k).φ w (((κ.1⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i i₀)‖ ^ 2 = 1 := by
  have hmem : (κ.1⁻¹ : GL ι 𝔸[k]) ∈ (adStd k).kGL ι := inv_mem κ.2
  obtain ⟨-, hU⟩ := hmem
  have h1 := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp (hU w)) i₀) i₀
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  have h2 : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  simp only [Matrix.star_apply, Matrix.map_apply, h2] at h1
  exact_mod_cast h1

def Hr (c : ℝ) (t : 𝔸[k]) : ℝ :=
  Real.smoothTransition (c - q₀ (homeomorphMixedSpace k t.1)) * if IntF t.2 then 1 else 0

theorem Hr_nonneg (c : ℝ) (t : 𝔸[k]) : 0 ≤ Hr c t := by
  unfold Hr
  refine mul_nonneg (Real.smoothTransition.nonneg _) ?_
  split_ifs <;> norm_num

theorem tensor_apply {ι : Type} [Fintype ι] (c : ℝ) (φ : 𝓢(ι → mixedSpace k, ℂ))
    (hφ : ∀ u, φ u = (Real.smoothTransition (c - qI u) : ℂ)) (x : ι → 𝔸[k]) :
    schwartzBruhatTensorPi φ
        (finiteTensor fun _ => cosetIndicator (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 0) x =
      (Real.smoothTransition (c - qI (infPartPi x)) : ℂ) * if ∀ i, IntF (x i).2 then 1 else 0 := by
  show φ (infPartPi x) * ∏ i, cosetIndicator (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 0 (x i).2 = _
  rw [hφ]
  simp only [ind_apply]
  congr 1
  rw [Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies]

theorem tensor_unit (c : ℝ) (φ : 𝓢(Unit → mixedSpace k, ℂ))
    (hφ : ∀ u, φ u = (Real.smoothTransition (c - qI u) : ℂ)) (t : 𝔸[k]) :
    schwartzBruhatTensorPi φ
        (finiteTensor fun _ => cosetIndicator (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 0) (fun _ => t) =
      (Hr c t : ℂ) := by
  have hq : qI (infPartPi (fun _ : Unit => t)) = q₀ (homeomorphMixedSpace k t.1) := by
    unfold qI
    exact Fintype.sum_unique _
  rw [tensor_apply c φ hφ (fun _ => t), hq]
  by_cases h : IntF t.2
  · simp [h, Hr]
  · simp [h, Hr]

theorem tensor_line {ι : Type} [Fintype ι] [DecidableEq ι] (c : ℝ) (φ : 𝓢(ι → mixedSpace k, ℂ))
    (hφ : ∀ u, φ u = (Real.smoothTransition (c - qI u) : ℂ)) (i₀ : ι) (κ : (adStd k).kGL ι)
    (t : 𝔸[k]) :
    schwartzBruhatTensorPi φ
        (finiteTensor fun _ => cosetIndicator (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 0)
        (t • (((κ.1⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ 1)) = (Hr c t : ℂ) := by
  have hcol : ((κ.1⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ 1 =
      fun i => ((κ.1⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i i₀ := by
    rw [Matrix.mulVec_single_one]
    rfl
  have hinv : (κ.1⁻¹ : GL ι 𝔸[k]) ∈ (adStd k).kGL ι := inv_mem κ.2
  obtain ⟨hO, -⟩ := hinv
  have hκ : κ.1 ∈ (adStd k).kGL ι := κ.2
  obtain ⟨hO', -⟩ := hκ
  have hone : (κ.1 : Matrix ι ι 𝔸[k]) * ((κ.1⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 := congrFun (congrFun hone i₀) i₀
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  have hI := intF_line (fun i => ((κ.1⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i i₀)
    (fun i => (κ.1 : Matrix ι ι 𝔸[k]) i₀ i) (fun i => (hO i i₀).1) (fun i => (hO' i₀ i).1) h1 t
  have hq := qI_line (fun i => ((κ.1⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i i₀) (col_norm κ i₀) t
  rw [hcol, tensor_apply c φ hφ, hq]
  have hI' : (∀ i, IntF ((t • fun i => ((κ.1⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i i₀) i).2) ↔ IntF t.2 := hI
  by_cases h : IntF t.2
  · rw [if_pos (hI'.mpr h)]
    simp [Hr, h]
  · rw [if_neg (fun h' => h (hI'.mp h'))]
    simp [Hr, h]

theorem zeta_ne (c : ℝ) (hc : (Fintype.card (InfinitePlace k) : ℝ) + 1 ≤ c)
    (φ : 𝓢(mixedSpace k, ℂ)) (hφ : ∀ u, φ u = (Real.smoothTransition (c - q₀ u) : ℂ))
    {x : ℝ} (hx : 1 < x) :
    globalZeta (fun t : 𝔸[k] => (Hr c t : ℂ)) 1 x ≠ 0 := by
  have hF : (fun t : 𝔸[k] => (Hr c t : ℂ)) = GroundTheory.Global.schwartzBruhatTensor φ
      (cosetIndicator (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 0) := by
    funext t
    show _ = φ (homeomorphMixedSpace k t.1) * cosetIndicator (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 0 t.2
    rw [hφ, ind_apply]
    by_cases h : IntF t.2 <;> simp [Hr, h]
  have hmem : (fun t : 𝔸[k] => (Hr c t : ℂ)) ∈ GroundTheory.Global.schwartzBruhat k := by
    rw [hF]
    exact GroundTheory.Global.schwartzBruhatTensor_mem φ (GroundTheory.Global.cosetIndicator_mem_finiteSchwartzBruhat _ _)
  have hint := GroundTheory.Global.integrable_globalZetaIntegrand hmem 1 (s := (x : ℂ)) (by simpa using hx)
  have hcont := GroundTheory.Global.continuous_zetaIntegrand
    (GroundTheory.Global.continuous_of_mem_schwartzBruhat hmem) 1 (x : ℂ)
  have hval : ∀ y : GroundTheory.Global.IdeleGroup k,
      RCLike.re ((fun t : 𝔸[k] => (Hr c t : ℂ)) (y : 𝔸[k]) *
        (((1 : GroundTheory.Global.HeckeCharacter k).toIdele y : Circle) : ℂ) *
        (((GroundTheory.Global.IdeleGroup.ideleModule k y : ℝ) : ℂ)) ^ (x : ℂ)) =
      Hr c (y : 𝔸[k]) * (GroundTheory.Global.IdeleGroup.ideleModule k y : ℝ) ^ x := by
    intro y
    have h1 : (1 : GroundTheory.Global.HeckeCharacter k).toIdele y = 1 := rfl
    rw [h1, ← Complex.ofReal_cpow (le_of_lt (GroundTheory.Global.IdeleGroup.ideleModule k y).2)]
    simp
  have hnn : ∀ y : GroundTheory.Global.IdeleGroup k, 0 ≤ RCLike.re ((fun t : 𝔸[k] => (Hr c t : ℂ)) (y : 𝔸[k]) *
        (((1 : GroundTheory.Global.HeckeCharacter k).toIdele y : Circle) : ℂ) *
        (((GroundTheory.Global.IdeleGroup.ideleModule k y : ℝ) : ℂ)) ^ (x : ℂ)) := fun y => by
    rw [hval]
    exact mul_nonneg (Hr_nonneg c _) (Real.rpow_nonneg (le_of_lt (GroundTheory.Global.IdeleGroup.ideleModule k y).2) x)
  have hq1 : q₀ (homeomorphMixedSpace k (1 : 𝔸[k]).1) = Fintype.card (InfinitePlace k) := by
    rw [q₀_inf]
    simp
  have hI1 : IntF (1 : 𝔸[k]).2 := (mem_intAd_iff 1).mp (Subring.one_mem _)
  have hs1 : Real.smoothTransition (c - q₀ (homeomorphMixedSpace k (1 : 𝔸[k]).1)) = 1 :=
    Real.smoothTransition.one_of_one_le (by rw [hq1]; linarith)
  have h1pos : 0 < RCLike.re ((fun t : 𝔸[k] => (Hr c t : ℂ)) ((1 : GroundTheory.Global.IdeleGroup k) : 𝔸[k]) *
        (((1 : GroundTheory.Global.HeckeCharacter k).toIdele 1 : Circle) : ℂ) *
        (((GroundTheory.Global.IdeleGroup.ideleModule k 1 : ℝ) : ℂ)) ^ (x : ℂ)) := by
    rw [hval]
    have hu : ((1 : GroundTheory.Global.IdeleGroup k) : 𝔸[k]) = 1 := rfl
    have hm : (GroundTheory.Global.IdeleGroup.ideleModule k 1 : ℝ) = 1 := by
      rw [map_one]
      rfl
    rw [hu, hm, Real.one_rpow, mul_one]
    unfold Hr
    rw [hs1, if_pos hI1]
    norm_num
  have hpos := (MeasureTheory.integral_pos_iff_support_of_nonneg (fun y => hnn y) hint.re).mpr
    ((Complex.continuous_re.comp hcont).isOpen_support.measure_pos _ ⟨1, h1pos.ne'⟩)
  rw [integral_re hint] at hpos
  intro h0
  delta GroundTheory.Global.globalZeta at h0
  rw [h0] at hpos
  simp at hpos

theorem testSph : TestSph := by
  intro k _ _ ι _ _ i₀
  set c : ℝ := (Fintype.card (InfinitePlace k) : ℝ) + 1 with hcdef
  have hc1 : (1 : ℝ) ≤ c := by
    have := (Nat.cast_nonneg (Fintype.card (InfinitePlace k)) : (0 : ℝ) ≤ _)
    linarith
  obtain ⟨φ, hφ⟩ := exists_bump (E := ι → mixedSpace k) (qI (k := k) (ι := ι)) contDiff_qI isBounded_qI c
  obtain ⟨φ₁, hφ₁⟩ := exists_bump (E := Unit → mixedSpace k) (qI (k := k) (ι := Unit)) contDiff_qI
    isBounded_qI c
  obtain ⟨φ₀, hφ₀⟩ := exists_bump (E := mixedSpace k) (q₀ (k := k)) contDiff_q₀ isBounded_q₀ c
  have hg : ∀ (κ : Type) [Fintype κ],
      finiteTensor (fun _ : κ => cosetIndicator (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 0) ∈
        finiteSchwartzBruhatPi k :=
    fun κ _ => finiteTensor_mem fun _ => GroundTheory.Global.cosetIndicator_mem_finiteSchwartzBruhat _ _
  refine ⟨schwartzBruhatTensorPi φ (finiteTensor fun _ => cosetIndicator (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 0),
    schwartzBruhatTensorPi φ₁ (finiteTensor fun _ => cosetIndicator (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 0),
    schwartzBruhatTensorPi_mem φ (hg ι), schwartzBruhatTensorPi_mem φ₁ (hg Unit), ?_, ?_, ?_⟩
  · rw [tensor_apply c φ hφ]
    have hq : qI (infPartPi (0 : ι → 𝔸[k])) = 0 := by
      unfold qI
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [show infPartPi (0 : ι → 𝔸[k]) i = homeomorphMixedSpace k (0 : 𝔸[k]).1 from rfl, q₀_inf]
      simp
    have hI : ∀ i, IntF ((0 : ι → 𝔸[k]) i).2 := fun i => (mem_intAd_iff 0).mp (Subring.zero_mem _)
    rw [hq, if_pos hI, sub_zero, Real.smoothTransition.one_of_one_le hc1]
    simp
  · intro t κ
    rw [tensor_line c φ hφ i₀ κ t, tensor_unit c φ₁ hφ₁ t]
  · intro x hx
    have hfun : (fun t : 𝔸[k] => schwartzBruhatTensorPi φ₁
        (finiteTensor fun _ => cosetIndicator (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 0) (fun _ => t)) =
        fun t => (Hr c t : ℂ) := funext fun t => tensor_unit c φ₁ hφ₁ t
    rw [hfun]
    exact zeta_ne c hcdef.symm.le φ₀ hφ₀ hx

end GlobalTheory.CompanionTheory.RgEisTestSph
