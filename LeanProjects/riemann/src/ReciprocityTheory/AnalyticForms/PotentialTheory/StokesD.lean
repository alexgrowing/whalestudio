import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesC
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology Set
open ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

section Leibniz

variable {D : ℕ}

theorem st_fderiv_cplx {f : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} {L : (Fin D → ℂ) →L[ℝ] ℝ}
    (hf : HasFDerivAt f L y) (d : Fin D → ℂ) :
    fderiv ℝ (cplx f) y d = ((L d : ℝ) : ℂ) := by
  have h : HasFDerivAt (cplx f) (Complex.ofRealCLM.comp L) y := by
    unfold cplx
    exact Complex.ofRealCLM.hasFDerivAt.comp y hf
  rw [h.fderiv]
  simp

theorem st_dz_cplx {f : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} {L : (Fin D → ℂ) →L[ℝ] ℝ}
    (hf : HasFDerivAt f L y) (j : Fin D) :
    dz j (cplx f) y = (((L (Pi.single j 1) : ℝ) : ℂ) -
      Complex.I * ((L (Complex.I • Pi.single j 1) : ℝ) : ℂ)) / 2 := by
  simp only [dz, st_fderiv_cplx hf]

theorem st_dzb_cplx {f : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} {L : (Fin D → ℂ) →L[ℝ] ℝ}
    (hf : HasFDerivAt f L y) (j : Fin D) :
    dzb j (cplx f) y = (((L (Pi.single j 1) : ℝ) : ℂ) +
      Complex.I * ((L (Complex.I • Pi.single j 1) : ℝ) : ℂ)) / 2 := by
  simp only [dzb, st_fderiv_cplx hf]

theorem st_gradDens_leibniz {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    (a b c : (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) (ha : DifferentiableAt ℝ a y)
    (hb : DifferentiableAt ℝ b y) (hc : c =ᶠ[𝓝 y] fun z => a z * b z) :
    gradDens φ c b y = a y * gradDens φ b b y + gradDens φ a (fun z => 1 / 2 * (b z * b z)) y := by
  have hLa := ha.hasFDerivAt
  have hLb := hb.hasFDerivAt
  have hc' : HasFDerivAt c (a y • fderiv ℝ b y + b y • fderiv ℝ a y) y :=
    (hLa.mul hLb).congr_of_eventuallyEq hc
  have hbb : HasFDerivAt (fun z => 1 / 2 * (b z * b z))
      ((1 / 2 : ℝ) • (b y • fderiv ℝ b y + b y • fderiv ℝ b y)) y :=
    (hLb.mul hLb).const_mul (1 / 2)
  have e1 : ∀ j, dz j (cplx c) y = (a y : ℂ) * dz j (cplx b) y + (b y : ℂ) * dz j (cplx a) y := by
    intro j
    rw [st_dz_cplx hc', st_dz_cplx hLb, st_dz_cplx hLa]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Complex.ofReal_add, Complex.ofReal_mul]
    ring
  have e2 : ∀ k, dzb k (cplx (fun z => 1 / 2 * (b z * b z))) y = (b y : ℂ) * dzb k (cplx b) y := by
    intro k
    rw [st_dzb_cplx hbb, st_dzb_cplx hLb]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Complex.ofReal_add, Complex.ofReal_mul]
    push_cast
    ring
  have hmat : gradMat c b y = (a y : ℂ) • gradMat b b y + gradMat a (fun z => 1 / 2 * (b z * b z)) y := by
    ext j k
    simp only [gradMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, e1, e2]
    ring
  simp only [gradDens]
  rw [hmat, mdisc_cons_eq_sum, mdisc_cons_eq_sum, mdisc_cons_eq_sum]
  have hs : ∑ j, ∑ k, ((a y : ℂ) • gradMat b b y + gradMat a (fun z => 1 / 2 * (b z * b z)) y) j k *
        mixedCof (fun i => hessC (φ i) y) j k =
      (a y : ℂ) * ∑ j, ∑ k, gradMat b b y j k * mixedCof (fun i => hessC (φ i) y) j k +
        ∑ j, ∑ k, gradMat a (fun z => 1 / 2 * (b z * b z)) y j k * mixedCof (fun i => hessC (φ i) y) j k := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  rw [hs, Complex.add_re, Complex.re_ofReal_mul]
  ring

end Leibniz

variable {e : ℕ} {X : Type} [TopologicalSpace X]

section Piece

variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))

include hΦ hGo hG hGU in

theorem st_partsHyp_piece (w ψ : X → ℝ) (hw : A.Smooth w) (hψ : A.Smooth ψ)
    (hψG : tsupport ψ ⊆ G) :
    PartsHyp (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
      ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) (w ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) := by
  have h3 : (3 : WithTop ℕ∞) ≤ ∞ := by
    first
    | exact_mod_cast (le_top : (3 : ℕ∞) ≤ ⊤)
    | exact WithTop.coe_le_coe.mpr le_top
    | norm_num
    | simp
  have hUo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) :=
    (A.chart j).isOpen_inter_preimage_symm hGo
  have hKc : IsCompact (tsupport ψ) := (isClosed_tsupport ψ).isCompact
  have hK : IsCompact ((A.chart j) '' tsupport ψ) :=
    hKc.image_of_continuousOn ((A.chart j).continuousOn.mono (hψG.trans hG))
  have hsupp : Function.support ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) ⊆
      (A.chart j) '' tsupport ψ := by
    intro y hy
    obtain ⟨ht, hs⟩ := Set.indicator_apply_ne_zero.mp hy
    exact ⟨(A.chart j).symm y, subset_tsupport _ hs, (A.chart j).right_inv ht⟩
  have htsK : tsupport ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) ⊆
      (A.chart j) '' tsupport ψ := closure_minimal hsupp hK.isClosed
  have hKU : (A.chart j) '' tsupport ψ ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G := by
    rintro _ ⟨x, hx, rfl⟩
    have hxs := hG (hψG hx)
    refine ⟨(A.chart j).map_source hxs, ?_⟩
    show (A.chart j).symm (A.chart j x) ∈ G
    rw [(A.chart j).left_inv hxs]
    exact hψG hx
  refine ⟨hUo, ?_, ?_, htsK.trans hKU, ?_, fun i => ?_⟩
  · exact (((hψ j).mono fun y hy => ⟨hy.1, Set.mem_univ _⟩).congr
      fun y hy => Set.indicator_of_mem hy.1 _).of_le h3
  · exact hK.of_isClosed_subset (isClosed_tsupport _) htsK
  · exact ((hw j).mono fun y hy => ⟨hy.1, Set.mem_univ _⟩).of_le h3
  · exact (((hΦ i).1 (x0 i) j).mono fun y hy => ⟨hy.1, hGU i hy.2⟩).of_le h3

include hΦ hGo hG hGU in

theorem st_nonpos_piece (hP : PartsStatement) (v θ : X → ℝ) (hv : A.Smooth v)
    (hθ : A.Smooth θ) (hθG : tsupport θ ⊆ G) :
    mInt A (Fin.cons (LocPot.ofFun v) Φ) (fun x => θ x * v x) =
      -(∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
          (A.chart j).target.indicator (θ ∘ (A.chart j).symm) y *
            gradDens (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) (v ∘ (A.chart j).symm)
              (v ∘ (A.chart j).symm) y) +
        mInt A (Fin.cons (LocPot.ofFun fun x => 1 / 2 * (v x * v x)) Φ) θ := by
  have h1 : (1 : WithTop ℕ∞) ≤ ∞ := by
    first
    | exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)
    | exact WithTop.coe_le_coe.mpr le_top
    | norm_num
    | simp
  have hUo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) :=
    (A.chart j).isOpen_inter_preimage_symm hGo
  have hUm := hUo.measurableSet
  have hθv : A.Smooth (fun x => θ x * v x) := st_smooth_mul A hθ hv
  have hθvG : tsupport (fun x => θ x * v x) ⊆ G := (tsupport_mul_subset_left).trans hθG
  have hvv : A.Smooth (fun x => v x * v x) := st_smooth_mul A hv hv
  have hv2 : A.Smooth (fun x => 1 / 2 * (v x * v x)) :=
    (smoothOnAlg A Set.univ Set.univ _ _ (1 / 2) hvv hvv subset_rfl).2
  have hL := st_left_piece (A := A) (Φ := Φ) (j := j) (G := G) (x0 := x0) (hΦ := hΦ) (hGo := hGo) (hG := hG) (hGU := hGU) v (fun x => θ x * v x) hv hθv hθvG
  have hR := st_left_piece (A := A) (Φ := Φ) (j := j) (G := G) (x0 := x0) (hΦ := hΦ) (hGo := hGo) (hG := hG) (hGU := hGU) (fun x => 1 / 2 * (v x * v x)) θ hv2 hθ hθG
  have P1 := hP e (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
    ((A.chart j).target.indicator ((fun x => θ x * v x) ∘ (A.chart j).symm)) (v ∘ (A.chart j).symm)
    ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G)
    (st_partsHyp_piece A Φ hΦ j G hGo hG x0 hGU v (fun x => θ x * v x) hv hθv hθvG)
  have P2 := hP e (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
    ((A.chart j).target.indicator (θ ∘ (A.chart j).symm)) ((fun x => 1 / 2 * (v x * v x)) ∘ (A.chart j).symm)
    ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G)
    (st_partsHyp_piece A Φ hΦ j G hGo hG x0 hGU (fun x => 1 / 2 * (v x * v x)) θ hv2 hθ hθG)
  have e1 : mInt A (Fin.cons (LocPot.ofFun v) Φ) (fun x => θ x * v x) =
      -gradInt (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
        ((A.chart j).target.indicator ((fun x => θ x * v x) ∘ (A.chart j).symm)) (v ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) := hL.trans P1.2.2.2.1
  have e2 : mInt A (Fin.cons (LocPot.ofFun fun x => 1 / 2 * (v x * v x)) Φ) θ =
      -gradInt (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
        ((A.chart j).target.indicator (θ ∘ (A.chart j).symm))
        ((fun x => 1 / 2 * (v x * v x)) ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) := hR.trans P2.2.2.2.1
  have hdiff : ∀ (f : X → ℝ), A.Smooth f → ∀ y ∈ (A.chart j).target,
      DifferentiableAt ℝ (f ∘ (A.chart j).symm) y := by
    intro f hf y hy
    have hm : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ ∈ 𝓝 y :=
      Filter.inter_mem ((A.chart j).open_target.mem_nhds hy) (by simp)
    exact ((hf j).contDiffAt hm).differentiableAt (by simp)
  have hlb : ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
      gradDens (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
        ((A.chart j).target.indicator ((fun x => θ x * v x) ∘ (A.chart j).symm)) (v ∘ (A.chart j).symm) y =
      (A.chart j).target.indicator (θ ∘ (A.chart j).symm) y *
          gradDens (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) (v ∘ (A.chart j).symm)
            (v ∘ (A.chart j).symm) y +
        gradDens (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
          ((A.chart j).target.indicator (θ ∘ (A.chart j).symm))
          ((fun x => 1 / 2 * (v x * v x)) ∘ (A.chart j).symm) y := by
    intro y hy
    have hnt : (A.chart j).target ∈ 𝓝 y := (A.chart j).open_target.mem_nhds hy.1
    have ha : DifferentiableAt ℝ ((A.chart j).target.indicator (θ ∘ (A.chart j).symm)) y := by
      refine (hdiff θ hθ y hy.1).congr_of_eventuallyEq ?_
      filter_upwards [hnt] with z hz
      exact Set.indicator_of_mem hz _
    have hc : (A.chart j).target.indicator ((fun x => θ x * v x) ∘ (A.chart j).symm) =ᶠ[𝓝 y]
        fun z => (A.chart j).target.indicator (θ ∘ (A.chart j).symm) z * (v ∘ (A.chart j).symm) z := by
      filter_upwards [hnt] with z hz
      simp [Set.indicator_of_mem hz]
    exact st_gradDens_leibniz _ _ _ _ y ha (hdiff v hv y hy.1) hc
  have hT1 : ∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
        (A.chart j).target.indicator (θ ∘ (A.chart j).symm) y *
          gradDens (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) (v ∘ (A.chart j).symm)
            (v ∘ (A.chart j).symm) y =
      gradInt (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
          ((A.chart j).target.indicator ((fun x => θ x * v x) ∘ (A.chart j).symm)) (v ∘ (A.chart j).symm)
          ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) -
        gradInt (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
          ((A.chart j).target.indicator (θ ∘ (A.chart j).symm))
          ((fun x => 1 / 2 * (v x * v x)) ∘ (A.chart j).symm)
          ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) := by
    rw [gradInt, gradInt, ← integral_sub P1.2.2.1 P2.2.2.1]
    refine setIntegral_congr_fun hUm fun y hy => ?_
    rw [hlb y hy]
    ring
  rw [e1, e2, hT1]
  ring

end Piece

private theorem mInt_cons_const_eq_zero (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (c : ℝ) (g : X → ℝ) :
    mInt A (Fin.cons (LocPot.ofFun fun _ => c) Φ) g = 0 := by
  have hL : ∀ j y, locDens A (Fin.cons (LocPot.ofFun fun _ => c) Φ) j y =
      locDens A (Fin.cons ((LocPot.ofFun fun _ => c).rsmul 0) Φ) j y := by
    intro j y
    have hf : ∀ c' : ℝ, fderiv ℝ (fderiv ℝ (fun _ : Fin (e + 1) → ℂ => c')) y = 0 := by
      intro c'
      have h0 : fderiv ℝ (fun _ : Fin (e + 1) → ℂ => c') = fun _ => 0 :=
        funext fun x => fderiv_const_apply c'
      rw [h0]
      exact fderiv_const_apply _
    have hz : ∀ c' : ℝ, hessC (fun _ : Fin (e + 1) → ℂ => c') y = 0 := by
      intro c'
      funext a b
      simp only [hessC, hf c']
      simp
    simp only [locDens, maDens]
    congr 3
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [Fin.cons_zero, LocPot.ofFun, LocPot.rsmul, zero_mul]
      rw [hz c, hz 0]
    · simp
  have h := mIntRsmul A 0 (LocPot.ofFun fun _ => c) Φ
    (isPotential_ofFun A _ fun j => contDiffOn_const) hΦ g
  rw [zero_mul] at h
  rw [← h]
  simp only [mInt, integralWith, hL]

theorem st_stokes_of (hP : PartsStatement) : StokesStatement := by
  intro e X _ _ _ A w hw Φ hΦ
  have h1 : A.Smooth (fun _ : X => (1 : ℝ)) := fun j => contDiffOn_const
  rw [st_byPartsSymm_of hP A (fun _ => 1) w h1 hw Φ hΦ]
  exact mInt_cons_const_eq_zero A Φ hΦ 1 w

private theorem mInt_finset_sum [CompactSpace X] [T2Space X] {d : ℕ} (A : FinHolAtlas d X)
    (Ψ : Fin d → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) {M : ℕ} (f : Fin M → X → ℝ)
    (hf : ∀ m, Continuous (f m)) (s : Finset (Fin M)) :
    mInt A Ψ (fun x => ∑ m ∈ s, f m x) = ∑ m ∈ s, mInt A Ψ (f m) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := mIntLinear A Ψ hΨ (-1) (fun _ => 0) (fun _ => 0)
      (mIntegrableCont A Ψ hΨ _ continuous_const) (mIntegrableCont A Ψ hΨ _ continuous_const)
    simp only [mul_zero, add_zero] at h
    simp only [Finset.sum_empty]
    linarith
  | insert a s ha ih =>
    have h := mIntLinear A Ψ hΨ 1 (f a) (fun x => ∑ m ∈ s, f m x)
      (mIntegrableCont A Ψ hΨ _ (hf a))
      (mIntegrableCont A Ψ hΨ _ (continuous_finset_sum _ fun m _ => hf m))
    simp only [one_mul] at h
    simp only [Finset.sum_insert ha]
    rw [h, ih]

theorem st_byPartsNonpos_of (hP : PartsStatement) (hN : GradDensNonnegStatement) :
    ByPartsNonposStatement := by
  intro e X _ _ _ A v hv Φ hΦ hpsh
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := by
    first
    | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    | exact WithTop.coe_le_coe.mpr le_top
    | norm_num
    | simp
  obtain ⟨M, θ, G, j, x0, hθs, hθ0, hθ1, hθG, hGo, hGs, hGU⟩ := st_exists_good_partition A Φ
  have hvc := st_smooth_continuous A hv
  have hvv : A.Smooth (fun x => v x * v x) := st_smooth_mul A hv hv
  have hv2 : A.Smooth (fun x => 1 / 2 * (v x * v x)) :=
    (smoothOnAlg A Set.univ Set.univ _ _ (1 / 2) hvv hvv subset_rfl).2
  have hΦ' : ∀ i, IsPotential A ((Fin.cons (LocPot.ofFun v) Φ : Fin (e + 1) → LocPot X) i) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa using isPotential_ofFun A v hv
    · simpa using hΦ k
  have hΦ2 : ∀ i, IsPotential A
      ((Fin.cons (LocPot.ofFun fun x => 1 / 2 * (v x * v x)) Φ : Fin (e + 1) → LocPot X) i) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa using isPotential_ofFun A _ hv2
    · simpa using hΦ k
  have hsplit : mInt A (Fin.cons (LocPot.ofFun v) Φ) v =
      ∑ m, mInt A (Fin.cons (LocPot.ofFun v) Φ) (fun x => θ m x * v x) := by
    have hv' : v = fun x => ∑ m, θ m x * v x := funext fun x => by rw [← Finset.sum_mul, hθ1, one_mul]
    calc mInt A (Fin.cons (LocPot.ofFun v) Φ) v
        = mInt A (Fin.cons (LocPot.ofFun v) Φ) (fun x => ∑ m, θ m x * v x) := by
          congr 1
      _ = _ := mInt_finset_sum A _ hΦ' (fun m x => θ m x * v x)
          (fun m => (st_smooth_continuous A (hθs m)).mul hvc) Finset.univ
  have hpiece := fun m => st_nonpos_piece A Φ hΦ (j m) (G m) (hGo m) (hGs m) (x0 m) (hGU m) hP v (θ m)
    hv (hθs m) (hθG m)
  have hsum2 : ∑ m, mInt A (Fin.cons (LocPot.ofFun fun x => 1 / 2 * (v x * v x)) Φ) (θ m) = 0 := by
    rw [← mInt_finset_sum A _ hΦ2 θ (fun m => st_smooth_continuous A (hθs m)) Finset.univ]
    have h1 : (fun x => ∑ m, θ m x) = fun _ => 1 := funext hθ1
    rw [h1]
    exact st_stokes_of hP A _ hv2 Φ hΦ
  have hnn : ∀ m, 0 ≤ ∫ y in (A.chart (j m)).target ∩ (A.chart (j m)).symm ⁻¹' G m,
      (A.chart (j m)).target.indicator (θ m ∘ (A.chart (j m)).symm) y *
        gradDens (fun i => (Φ i).φ (x0 m i) ∘ (A.chart (j m)).symm) (v ∘ (A.chart (j m)).symm)
          (v ∘ (A.chart (j m)).symm) y := by
    intro m
    have hUo : IsOpen ((A.chart (j m)).target ∩ (A.chart (j m)).symm ⁻¹' G m) :=
      (A.chart (j m)).isOpen_inter_preimage_symm (hGo m)
    refine setIntegral_nonneg hUo.measurableSet fun y hy => mul_nonneg ?_ ?_
    · exact Set.indicator_nonneg (fun z _ => hθ0 m _) y
    · exact hN e _ _ _ hUo
        (fun i => (((hΦ i).1 (x0 m i) (j m)).mono fun z hz => ⟨hz.1, hGU m i hz.2⟩).of_le h2)
        (fun i z hz ξ => hpsh i (x0 m i) (j m) z ⟨hz.1, hGU m i hz.2⟩ ξ) y hy
  rw [hsplit, Finset.sum_congr rfl fun m _ => hpiece m, Finset.sum_add_distrib, hsum2, add_zero,
    Finset.sum_neg_distrib]
  exact neg_nonpos.mpr (Finset.sum_nonneg fun m _ => hnn m)

theorem st_mass_step (hP : PartsStatement) [CompactSpace X] [T2Space X] {n : ℕ}
    (A : FinHolAtlas (n + 1) X) (Ψ : Fin (n + 1) → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i))
    (i0 : Fin (n + 1)) (u : X → ℝ) (hu : A.Smooth u) :
    mInt A (Function.update Ψ i0 (Ψ i0 + LocPot.ofFun u)) (fun _ => 1) =
      mInt A Ψ (fun _ => 1) := by
  classical
  set Ψ' := Function.update Ψ i0 (Ψ i0 + LocPot.ofFun u) with hΨ'
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 i0
  have hne : ∀ i : Fin n, σ i.succ ≠ i0 := by
    intro i h
    have h2 := congrArg σ h
    simp only [σ, Equiv.swap_apply_self, Equiv.swap_apply_right] at h2
    exact Fin.succ_ne_zero i h2
  set Φ' : Fin n → LocPot X := fun i => Ψ (σ i.succ) with hΦ'
  have h1 : Ψ' ∘ σ = Fin.cons (Ψ i0 + LocPot.ofFun u) Φ' := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [σ, Ψ']
    · simp only [Function.comp, Fin.cons_succ, Φ', Ψ']
      rw [Function.update_of_ne (hne i)]
  have h2 : Ψ ∘ σ = Fin.cons (Ψ i0) Φ' := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [σ]
    · simp [Φ']
  have hPot' : ∀ i, IsPotential A (Φ' i) := fun i => hΨ _
  have hu' := isPotential_ofFun A u hu
  have hint : ∀ Q : LocPot X, IsPotential A Q → MIntegrable A (Fin.cons Q Φ') (fun _ => 1) := by
    intro Q hQ
    refine mIntegrableCont A _ ?_ _ continuous_const
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using hQ
    · simpa using hPot' i
  rw [← mIntSymm A Ψ' σ, h1, mIntAdd A _ _ Φ' (hΨ i0) hu' hPot' _ (hint _ (hΨ i0)) (hint _ hu'),
    st_stokes_of hP A u hu Φ' hPot', add_zero, ← h2, mIntSymm]

theorem st_massIndep_of (hP : PartsStatement) : MassIndepStatement := by
  intro e X _ _ _ A Φ u hΦ hu
  cases e with
  | zero =>
    congr 1
    funext i
    exact i.elim0
  | succ n =>
    classical
    have key : ∀ s : Finset (Fin (n + 1)),
        mInt A (fun i => if i ∈ s then Φ i + LocPot.ofFun (u i) else Φ i) (fun _ => 1) =
          mInt A Φ (fun _ => 1) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        have hpot : ∀ i, IsPotential A (if i ∈ s then Φ i + LocPot.ofFun (u i) else Φ i) := by
          intro i
          split_ifs
          · exact isPotentialAdd A _ _ (hΦ i) (isPotential_ofFun A _ (hu i))
          · exact hΦ i
        have hupd : (fun i => if i ∈ insert a s then Φ i + LocPot.ofFun (u i) else Φ i) =
            Function.update (fun i => if i ∈ s then Φ i + LocPot.ofFun (u i) else Φ i) a
              (Φ a + LocPot.ofFun (u a)) := by
          funext i
          by_cases hi : i = a
          · subst hi
            simp
          · simp [hi, Finset.mem_insert]
        have hstep := st_mass_step hP A (fun i => if i ∈ s then Φ i + LocPot.ofFun (u i) else Φ i)
          hpot a (u a) (hu a)
        simp only [ha, if_false] at hstep
        rw [hupd, hstep, ih]
    simpa using key Finset.univ

end

end ReciprocityTheory.AnForm.M
