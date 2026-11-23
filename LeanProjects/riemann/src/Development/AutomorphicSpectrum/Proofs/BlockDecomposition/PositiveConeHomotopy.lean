import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SuperHomot

variable {I : Type} [Fintype I] [DecidableEq I]

theorem setIntegral_fderiv_eq_zero {U C : Set (I → ℝ)} (hU : IsOpen U) (hCU : C ⊆ U) (hC : IsCompact C)
    (b : (I → ℝ) → ℂ) (hb : ContDiffOn ℝ 1 b U)
    (hz : ∀ v ∈ U, v ∉ C → ∀ᶠ w in nhds v, b w = 0) (w : I → ℝ) :
    ∫ v in C, fderiv ℝ b v w = 0 := by
  classical
  set f : (I → ℝ) → ℂ := U.indicator b with hf
  have hfU : ∀ v ∈ U, f =ᶠ[nhds v] b := fun v hv => by
    filter_upwards [hU.mem_nhds hv] with x hx using indicator_of_mem hx _
  have hfC : ∀ x, x ∉ C → f x = 0 := fun x hx => by
    by_cases hxU : x ∈ U
    · rw [hf, indicator_of_mem hxU]; exact (hz x hxU hx).self_of_nhds
    · rw [hf, indicator_of_notMem hxU]
  have hf0 : ∀ v, v ∉ C → f =ᶠ[nhds v] 0 := fun v hv => by
    filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hv] with x hx using hfC x hx
  have hfd : ContDiff ℝ 1 f := by
    rw [contDiff_iff_contDiffAt]
    intro v
    by_cases hv : v ∈ U
    · exact (hb.contDiffAt (hU.mem_nhds hv)).congr_of_eventuallyEq (hfU v hv)
    · exact contDiffAt_const.congr_of_eventuallyEq (hf0 v fun h => hv (hCU h))
  have hcs : HasCompactSupport f := HasCompactSupport.intro hC hfC
  have hi : Integrable (fun v => fderiv ℝ f v w) := by
    have h1 : Continuous fun v => fderiv ℝ f v w := (hfd.continuous_fderiv one_ne_zero).clm_apply continuous_const
    refine h1.integrable_of_hasCompactSupport ((hcs.fderiv (𝕜 := ℝ)).mono ?_)
    intro z hz'
    rw [Function.mem_support] at hz' ⊢
    intro h; apply hz'; rw [h]; rfl
  have h0 : ∫ v, fderiv ℝ f v w = 0 := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun _ => (1 : ℂ)) (g := f) (v := w) (by simp) (by simpa using hi)
      (by simpa using hfd.continuous.integrable_of_hasCompactSupport hcs)
      (fun _ _ => differentiableAt_const _) (fun x _ => (hfd.differentiable one_ne_zero) x)
    simpa using h
  have h2 : ∫ v in C, fderiv ℝ f v w = ∫ v, fderiv ℝ f v w :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [(hf0 x hx).fderiv_eq]; simp
  rw [← h0, ← h2]
  refine setIntegral_congr_fun hC.measurableSet fun v hv => ?_
  rw [(hfU v (hCU hv)).fderiv_eq]

theorem key_alg {W : Type*} [Ring W] [Algebra ℂ W] (tr : W →ₗ[ℂ] ℂ) (htr : ∀ X Y, tr (X * Y) = tr (Y * X))
    (e c L1 L2 : I → W) (Γ Sv k : W) (s : ℂ) (x : I → ℂ)
    (hec : ∀ i j, e i * c j + c j * e i = if i = j then 1 else 0)
    (hΓc : ∀ i, Γ * c i = -(c i * Γ))
    (hΓS : Γ * Sv = Sv * Γ) (hSe : ∀ i, Sv * e i = s • (e i * Sv))
    (hΓL : ∀ i, Γ * L2 i = L2 i * Γ)
    (hch : ∑ i, e i * L1 i + ∑ i, L2 i * e i = 0) :
    tr (Γ * (∑ i, e i * Sv * c i) * k) + tr (Γ * Sv * ∑ i, x i • L1 i) =
      ∑ i, (tr (Γ * e i * Sv * c i * k) +
        tr (Γ * e i * Sv * (∑ j, x j • c j) * (s • L1 i + L2 i))) := by
  set J := ∑ j, x j • c j with hJ
  have hΓJ : Γ * J = -(J * Γ) := by
    simp only [hJ, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, mul_smul_comm, smul_mul_assoc, hΓc, smul_neg]
  have hanti : ∀ i, e i * J + J * e i = x i • 1 := by
    intro i
    simp only [hJ, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, ← Finset.sum_add_distrib, ← smul_add, hec]
    simp
  have h1 : ∀ i, tr (Γ * e i * Sv * J * (s • L1 i)) = tr (Γ * Sv * (e i * J * L1 i)) := by
    intro i
    have h : Γ * e i * Sv * J * (s • L1 i) = Γ * (s • (e i * Sv)) * J * L1 i := by
      simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    rw [h, ← hSe]; simp only [mul_assoc]
  have h2 : ∀ i, tr (Γ * e i * Sv * J * L2 i) = - tr (Γ * Sv * (J * (L2 i * e i))) := by
    intro i
    rw [show Γ * e i * Sv * J * L2 i = (Γ * e i) * (Sv * J * L2 i) by simp only [mul_assoc], htr]
    have h : Sv * J * L2 i * (Γ * e i) = -(Γ * Sv * (J * (L2 i * e i))) := by
      calc Sv * J * L2 i * (Γ * e i) = Sv * J * (L2 i * Γ) * e i := by simp only [mul_assoc]
        _ = Sv * (J * Γ) * L2 i * e i := by rw [← hΓL]; simp only [mul_assoc]
        _ = Sv * (-(Γ * J)) * L2 i * e i := by rw [hΓJ, neg_neg]
        _ = -((Sv * Γ) * J * L2 i * e i) := by simp only [mul_neg, neg_mul, mul_assoc]
        _ = _ := by rw [← hΓS]; simp only [mul_assoc]
    rw [h, map_neg]
  have hsum : ∑ i, L2 i * e i = -∑ i, e i * L1 i := eq_neg_of_add_eq_zero_right hch
  have h3 : ∑ i, tr (Γ * Sv * (J * (L2 i * e i))) = -∑ i, tr (Γ * Sv * (J * (e i * L1 i))) := by
    rw [← map_sum, ← map_sum, ← map_neg, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
    simp only [mul_neg]
  have h4 : tr (Γ * Sv * ∑ i, x i • L1 i) =
      ∑ i, tr (Γ * Sv * (e i * J * L1 i)) + ∑ i, tr (Γ * Sv * (J * (e i * L1 i))) := by
    rw [← Finset.sum_add_distrib]
    simp only [← map_add]
    rw [← map_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := hanti i
    rw [← mul_add]
    congr 1
    rw [← mul_assoc J, ← add_mul, h]
    simp
  have h5 : tr (Γ * (∑ i, e i * Sv * c i) * k) = ∑ i, tr (Γ * e i * Sv * c i * k) := by
    rw [← map_sum]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [h5, h4, Finset.sum_add_distrib]
  congr 1
  simp only [mul_add, map_add, h1, h2, Finset.sum_add_distrib, Finset.sum_neg_distrib, h3, neg_neg]

section Analytic

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def trC : (V →L[ℂ] V) →ₗ[ℂ] ℂ := (LinearMap.trace ℂ V).comp (ContinuousLinearMap.coeLM ℂ)

def trL : (V →L[ℂ] V) →L[ℝ] ℂ :=
  haveI : FiniteDimensional ℂ (V →L[ℂ] V) :=
    Module.Finite.equiv (LinearMap.toContinuousLinearMap : (V →ₗ[ℂ] V) ≃ₗ[ℂ] V →L[ℂ] V)
  (LinearMap.toContinuousLinearMap (trC (V := V))).restrictScalars ℝ

theorem trL_apply (X : V →L[ℂ] V) : trL X = LinearMap.trace ℂ V (X : V →ₗ[ℂ] V) := rfl

theorem trC_apply (X : V →L[ℂ] V) : trC X = trL X := rfl

theorem trC_mul_comm (X Y : V →L[ℂ] V) : trC (X * Y) = trC (Y * X) :=
  LinearMap.trace_mul_comm ℂ (X : V →ₗ[ℂ] V) (Y : V →ₗ[ℂ] V)

def path (o : I → ℝ) (s : ℝ) (v : I → ℝ) : (I → ℝ) × (I → ℝ) := (s • v + (1 - s) • o, v)

theorem hasDerivAt_A (K : (I → ℝ) × (I → ℝ) → (V →L[ℂ] V)) (S : ℝ → (V →L[ℂ] V)) (Γ : V →L[ℂ] V)
    (o v : I → ℝ) (s : ℝ) (hS : DifferentiableAt ℝ S s) (hK : DifferentiableAt ℝ K (path o s v)) :
    HasDerivAt (fun s => trL (Γ * S s * K (path o s v)))
      (trL (Γ * deriv S s * K (path o s v)) + trL (Γ * S s * fderiv ℝ K (path o s v) (v - o, 0))) s := by
  have hP : HasDerivAt (fun s => path o s v) (v - o, 0) s := by
    have h1 : HasDerivAt (fun s : ℝ => s • v + (1 - s) • o) (v - o) s := by
      have a : HasDerivAt (fun s : ℝ => s • v) v s := by simpa using (hasDerivAt_id s).smul_const v
      have b : HasDerivAt (fun s : ℝ => (1 - s) • o) (-o) s := by
        simpa using ((hasDerivAt_id s).const_sub 1).smul_const o
      have h : HasDerivAt (fun s : ℝ => s • v + (1 - s) • o) (v + -o) s := a.add b
      rwa [← sub_eq_add_neg] at h
    exact h1.prodMk (hasDerivAt_const s v)
  have hKP := hK.hasFDerivAt.comp_hasDerivAt s hP
  have hm : HasDerivAt (fun s => Γ * S s * K (path o s v))
      (Γ * deriv S s * K (path o s v) + Γ * S s * fderiv ℝ K (path o s v) (v - o, 0)) s :=
    (hS.hasDerivAt.const_mul Γ).mul hKP
  have ht := trL.hasFDerivAt.comp_hasDerivAt s hm
  rw [map_add] at ht
  exact ht

set_option maxHeartbeats 1000000 in
theorem fderiv_b (K : (I → ℝ) × (I → ℝ) → (V →L[ℂ] V)) (A : V →L[ℂ] V) (c : I → (V →L[ℂ] V))
    (o v w : I → ℝ) (s : ℝ) (hK : DifferentiableAt ℝ K (path o s v)) :
    fderiv ℝ (fun v => trL (A * (∑ j, (v - o) j • c j) * K (path o s v))) v w =
      trL (A * (∑ j, w j • c j) * K (path o s v)) +
        trL (A * (∑ j, (v - o) j • c j) * fderiv ℝ K (path o s v) (s • w, w)) := by
  set Jd : (I → ℝ) →L[ℝ] (V →L[ℂ] V) :=
    ∑ j, (ContinuousLinearMap.proj j : (I → ℝ) →L[ℝ] ℝ).smulRight (c j) with hJd
  have hJa : ∀ x, Jd x = ∑ j, x j • c j := fun x => by simp [hJd, ContinuousLinearMap.sum_apply]
  have hJ : HasFDerivAt (fun v => ∑ j, (v - o) j • c j) Jd v := by
    have h := Jd.hasFDerivAt.comp v ((hasFDerivAt_id v).sub_const o)
    have h2 : (⇑Jd ∘ fun x => id x - o) = fun v => ∑ j, (v - o) j • c j := by
      funext x; simp [hJa]
    rw [h2] at h
    simpa using h
  set Pd : (I → ℝ) →L[ℝ] (I → ℝ) × (I → ℝ) :=
    (s • ContinuousLinearMap.id ℝ (I → ℝ)).prod (ContinuousLinearMap.id ℝ (I → ℝ)) with hPd
  have hP : HasFDerivAt (path o s) Pd v := by
    have h := Pd.hasFDerivAt.add_const (x := v) (((1 - s) • o, 0) : (I → ℝ) × (I → ℝ))
    have h2 : (fun x => Pd x + (((1 - s) • o, 0) : (I → ℝ) × (I → ℝ))) = path o s := by
      funext x; simp [hPd, path]
    rwa [h2] at h
  have hKP := hK.hasFDerivAt.comp v hP
  have hm := (hJ.const_mul A).mul' hKP
  have ht0 := (trL (V := V)).hasFDerivAt.comp v hm
  have ht : HasFDerivAt (fun v => trL (A * (∑ j, (v - o) j • c j) * K (path o s v))) _ v := ht0
  rw [ht.fderiv]
  simp [hJa, hPd, add_comm]

theorem contDiffOn_b {U : Set (I → ℝ)} (K : (I → ℝ) × (I → ℝ) → (V →L[ℂ] V)) (A : V →L[ℂ] V)
    (c : I → (V →L[ℂ] V)) (o : I → ℝ) (s : ℝ) (hK : ContDiffOn ℝ ∞ K (U ×ˢ U))
    (hm : ∀ v ∈ U, path o s v ∈ U ×ˢ U) :
    ContDiffOn ℝ 1 (fun v => trL (A * (∑ j, (v - o) j • c j) * K (path o s v))) U := by
  have hp : ContDiff ℝ 1 (path o s : (I → ℝ) → _) := by
    unfold path; fun_prop
  have hKc : ContDiffOn ℝ 1 (fun v => K (path o s v)) U := (hK.of_le (by simp)).comp hp.contDiffOn hm
  have hJ : ContDiff ℝ 1 (fun v : I → ℝ => A * ∑ j, (v - o) j • c j) := by
    fun_prop
  exact trL.contDiff.comp_contDiffOn (hJ.contDiffOn.mul hKc)

theorem clm_fst_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : (I → ℝ) × (I → ℝ) →L[ℝ] E) (w : I → ℝ) :
    L (w, 0) = ∑ i, w i • L (Pi.single i 1, 0) := by
  have h : (w, (0 : I → ℝ)) = ∑ i, w i • ((Pi.single i 1 : I → ℝ), (0 : I → ℝ)) := by
    ext j
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  rw [h, map_sum]
  simp only [map_smul]

end Analytic

theorem homot : PositivityTheory.RgBcC.Homot := by
  intro I _ _ V _ _ _ e c S Γ U o K hU hconv ho hec hΓe hΓc hΓS hS hSe hSd hK hΓK hch hex
  obtain ⟨C, hCU, hC, hsupp⟩ := hex
  have hUU : IsOpen (U ×ˢ U) := hU.prod hU
  have hpath : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v ∈ U, path o s v ∈ U ×ˢ U := fun s hs v hv =>
    ⟨hconv hv ho hs.1 (by linarith [hs.2]) (by ring), hv⟩
  have hKd : ∀ y ∈ U ×ˢ U, DifferentiableAt ℝ K y := fun y hy =>
    (hK.contDiffAt (hUU.mem_nhds hy)).differentiableAt (by simp)
  have hSdiff : Differentiable ℝ S := hS.differentiable (by simp)
  have hSc : Continuous S := hS.continuous
  have hdS : Continuous (deriv S) := hS.continuous_deriv (by simp)
  have hPc : Continuous (fun p : ℝ × (I → ℝ) => path o p.1 p.2) := by
    unfold path; fun_prop
  have hPv : ∀ s, Continuous (path o s : (I → ℝ) → _) := fun s => by
    unfold path; fun_prop
  set D : ℝ → (I → ℝ) → ℂ := fun s v => trL (Γ * deriv S s * K (path o s v)) +
    trL (Γ * S s * fderiv ℝ K (path o s v) (v - o, 0)) with hD
  set A : ℝ → (I → ℝ) → ℂ := fun s v => trL (Γ * S s * K (path o s v)) with hA
  have hDc : ContinuousOn (Function.uncurry D) (Icc 0 1 ×ˢ U) := by
    have hmaps : MapsTo (fun p : ℝ × (I → ℝ) => path o p.1 p.2) (Icc 0 1 ×ˢ U) (U ×ˢ U) :=
      fun p hp => hpath _ hp.1 _ hp.2
    have hKc := hK.continuousOn.comp hPc.continuousOn hmaps
    have hFc := (hK.continuousOn_fderiv_of_isOpen hUU (by simp)).comp hPc.continuousOn hmaps
    have h1 : ContinuousOn (fun p : ℝ × (I → ℝ) => Γ * deriv S p.1) (Icc 0 1 ×ˢ U) :=
      Continuous.continuousOn (by fun_prop)
    have h2 : ContinuousOn (fun p : ℝ × (I → ℝ) => Γ * S p.1) (Icc 0 1 ×ˢ U) :=
      Continuous.continuousOn (by fun_prop)
    have h3 : ContinuousOn (fun p : ℝ × (I → ℝ) => ((p.2 - o, 0) : (I → ℝ) × (I → ℝ))) (Icc 0 1 ×ˢ U) :=
      Continuous.continuousOn (by fun_prop)
    exact (trL.continuous.comp_continuousOn (h1.mul hKc)).add
      (trL.continuous.comp_continuousOn (h2.mul (hFc.clm_apply h3)))
  have hFTC : ∀ v ∈ U, ∫ s in (0 : ℝ)..1, D s v = A 1 v - A 0 v := by
    intro v hv
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => A s v) (f' := fun s => D s v)
      (fun s hs => ?_) ?_
    · rw [uIcc_of_le zero_le_one] at hs
      exact hasDerivAt_A K S Γ o v s (hSdiff s) (hKd _ (hpath s hs v hv))
    · refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
      exact hDc.comp (f := fun s : ℝ => (s, v)) (Continuous.continuousOn (by fun_prop))
        (fun s hs => ⟨hs, hv⟩)
  have hcomm : ∀ y ∈ U ×ˢ U, ∀ w, Γ * fderiv ℝ K y w = fderiv ℝ K y w * Γ := by
    intro y hy w
    have h1 := (hKd y hy).hasFDerivAt.const_mul Γ
    have h2 := (hKd y hy).hasFDerivAt.mul_const' Γ
    have h3 : (fun y => Γ * K y) = fun y => K y * Γ := funext hΓK
    rw [h3] at h1
    have h4 := congrArg (fun L => L w) (h1.unique h2)
    simpa using h4
  have hdiv : ∀ s ∈ Icc (0 : ℝ) 1, ∫ v in C, D s v = 0 := by
    intro s hs
    set b : I → (I → ℝ) → ℂ := fun i v => trL (Γ * e i * S s * (∑ j, (v - o) j • c j) * K (path o s v)) with hb
    have hbd : ∀ i, ContDiffOn ℝ 1 (b i) U := fun i =>
      contDiffOn_b K (Γ * e i * S s) c o s hK (hpath s hs)
    have hz : ∀ i, ∀ v ∈ U, v ∉ C → ∀ᶠ w in nhds v, b i w = 0 := by
      intro i v hv hvC
      have h : ∀ᶠ y in nhds (path o s v), K y = 0 := hsupp s hs v hv hvC
      filter_upwards [((hPv s).tendsto v).eventually h] with w hw
      simp [hb, hw]
    have hpt : ∀ v ∈ U, D s v = ∑ i, fderiv ℝ (b i) v (Pi.single i 1) := by
      intro v hv
      have hy := hpath s hs v hv
      set y := path o s v with hydef
      have hk := key_alg (trC (V := V)) trC_mul_comm e c (fun i => fderiv ℝ K y (Pi.single i 1, 0))
        (fun i => fderiv ℝ K y (0, Pi.single i 1)) Γ (S s) (K y) (s : ℂ) (fun j => (((v - o) j : ℝ) : ℂ))
        hec hΓc (hΓS s) (fun i => hSe s i) (fun i => hcomm y hy _) (hch y hy)
      simp only [Complex.coe_smul, trC_apply] at hk
      have hfd : ∀ i, fderiv ℝ (b i) v (Pi.single i 1) =
          trL (Γ * e i * S s * c i * K y) +
            trL (Γ * e i * S s * (∑ j, (v - o) j • c j) *
              (s • fderiv ℝ K y (Pi.single i 1, 0) + fderiv ℝ K y (0, Pi.single i 1))) := by
        intro i
        have h := fderiv_b K (Γ * e i * S s) c o v (Pi.single i 1) s (hKd _ hy)
        have h1 : (∑ j, (Pi.single i (1 : ℝ) : I → ℝ) j • c j) = c i := by
          simp [Pi.single_apply]
        have h2 : fderiv ℝ K y (s • (Pi.single i 1 : I → ℝ), (Pi.single i 1 : I → ℝ)) =
            s • fderiv ℝ K y (Pi.single i 1, 0) + fderiv ℝ K y (0, Pi.single i 1) := by
          rw [← map_smul, ← map_add]
          simp
        rw [h1, ← hydef, h2] at h
        exact h
      simp only [hfd]
      rw [← hk, hD]
      simp only
      rw [hSd s, ← hydef, clm_fst_eq]
    have hcalc : ∫ v in C, D s v = ∑ i, ∫ v in C, fderiv ℝ (b i) v (Pi.single i 1) := by
      rw [setIntegral_congr_fun hC.measurableSet (fun v hv => hpt v (hCU hv))]
      refine integral_finset_sum _ fun i _ => ?_
      exact ((((hbd i).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).mono hCU).integrableOn_compact hC
    rw [hcalc]
    exact Finset.sum_eq_zero fun i _ => setIntegral_fderiv_eq_zero hU hCU hC (b i) (hbd i) (hz i) _
  have hAc : ∀ s ∈ Icc (0 : ℝ) 1, ContinuousOn (A s) U := fun s hs =>
    trL.continuous.comp_continuousOn (continuousOn_const.mul
      (hK.continuousOn.comp (hPv s).continuousOn (hpath s hs)))
  have hint : Integrable (Function.uncurry D) ((volume.restrict (uIoc (0 : ℝ) 1)).prod (volume.restrict C)) := by
    rw [Measure.prod_restrict, uIoc_of_le zero_le_one]
    have hc : IsCompact (Icc (0 : ℝ) 1 ×ˢ C) := isCompact_Icc.prod hC
    have h : IntegrableOn (Function.uncurry D) (Icc (0 : ℝ) 1 ×ˢ C) (volume.prod volume) :=
      (hDc.mono (prod_mono_right hCU)).integrableOn_compact hc
    exact h.mono_set (prod_mono_left Ioc_subset_Icc_self)
  have hz1 : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v ∈ U \ C, A s v = 0 := by
    intro s hs v hv
    have h : K (path o s v) = 0 := (hsupp s hs v hv.1 hv.2).self_of_nhds
    simp [hA, h]
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hgoal : ∫ v in U, A 1 v = ∫ v in U, A 0 v := by
    rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero hU.measurableSet hCU (hz1 1 h1),
      setIntegral_eq_of_subset_of_forall_diff_eq_zero hU.measurableSet hCU (hz1 0 h0),
      ← sub_eq_zero, ← integral_sub (((hAc 1 h1).mono hCU).integrableOn_compact hC)
        (((hAc 0 h0).mono hCU).integrableOn_compact hC)]
    calc ∫ v in C, (A 1 v - A 0 v) = ∫ v in C, ∫ s in (0 : ℝ)..1, D s v :=
          setIntegral_congr_fun hC.measurableSet (fun v hv => (hFTC v (hCU hv)).symm)
      _ = ∫ s in (0 : ℝ)..1, ∫ v in C, D s v := (intervalIntegral_integral_swap hint).symm
      _ = ∫ s in (0 : ℝ)..1, (0 : ℂ) := intervalIntegral.integral_congr fun s hs =>
          hdiv s (by rwa [uIcc_of_le zero_le_one] at hs)
      _ = 0 := by simp
  have hp1 : ∀ v, path o 1 v = (v, v) := fun v => by simp [path]
  have hp0 : ∀ v, path o 0 v = (o, v) := fun v => by simp [path]
  simp only [hA, hp1, hp0, trL_apply] at hgoal
  exact hgoal

end GlobalTheory.CompanionTheory.SuperHomot
