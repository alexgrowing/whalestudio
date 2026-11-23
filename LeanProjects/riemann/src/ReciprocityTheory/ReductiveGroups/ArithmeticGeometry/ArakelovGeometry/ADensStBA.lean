import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AParamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFS

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Topology
open scoped ComplexOrder

variable {κ : Type} [Fintype κ] {D : ℕ}

def evalConstSnd (w : ((k : Unit) → GlobalTheory κ k) → ℂ) : Ix κ → ℂ := fun p => w fun _ => p.2

theorem adbLift_segre (z : Ix κ → ℂ) : evalConstSnd (segre (ι := GlobalTheory κ) z) = z := by
  funext p
  simp [evalConstSnd, segre]

theorem adb_segre_smul (c : ℂ) (z : Ix κ → ℂ) :
    segre (ι := GlobalTheory κ) (c • z) = c • segre (ι := GlobalTheory κ) z := by
  funext p
  simp [segre]

theorem adb_segre_injective : Function.Injective (segre (ι := GlobalTheory κ)) := fun z z' h => by
  rw [← adbLift_segre z, h, adbLift_segre]

theorem adb_mem_mcPts_iff {P : Ideal (MRing (GlobalTheory κ))} {z : Ix κ → ℂ} :
    z ∈ mcPts (ι := GlobalTheory κ) P ↔ z ∈ pts P := by
  simp only [mcPts, pts, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hk, h⟩
    obtain ⟨i, hi⟩ := hk ()
    refine ⟨fun h0 => hi (by simp [h0]), h⟩
  · rintro ⟨hz, h⟩
    refine ⟨fun k => ?_, h⟩
    by_contra hc
    push_neg at hc
    exact hz (funext fun p => hc p.2)

def IsSheetParamB (P : Ideal (MRing (GlobalTheory κ)))
    (Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ))
    (U : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → Ix κ → ℂ) : Prop :=
  IsParam P U γ ∧ ∀ y ∈ U, Ψ (segre (ι := GlobalTheory κ) (γ y)) = Fin.cons 1 y

variable {P : Ideal (MRing (GlobalTheory κ))} {Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)}
  {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → Ix κ → ℂ}

theorem adb_mem_coneOver_self {y : Fin D → ℂ} (hy : y ∈ U) : γ y ∈ coneOver U γ :=
  ⟨y, hy, 1, one_ne_zero, by simp⟩

theorem IsSheetParamB.eq_of_mem (hs : IsSheetParamB P Ψ U γ) {z : Ix κ → ℂ}
    (hz : z ∈ coneOver U γ) {y : Fin D → ℂ} (hΨ : Ψ (segre (ι := GlobalTheory κ) z) = Fin.cons 1 y) :
    y ∈ U ∧ z = γ y := by
  obtain ⟨y0, hy0, c, hc, rfl⟩ := hz
  have h1 := hs.2 y0 hy0
  rw [adb_segre_smul, map_smul, h1] at hΨ
  have h0 := congrFun hΨ 0
  simp only [Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one] at h0
  subst h0
  rw [one_smul] at hΨ
  have hyy : y0 = y := by
    funext i
    have := congrFun hΨ i.succ
    simpa using this
  subst hyy
  exact ⟨hy0, by rw [one_smul]⟩

theorem IsSheetParamB.isSheet (hs : IsSheetParamB P Ψ U γ) {y : Fin D → ℂ} (hy : y ∈ U) :
    IsSheet P Ψ y (segre (ι := GlobalTheory κ) (γ y)) γ := by
  obtain ⟨⟨hU, hγ, hpts, -⟩, hΨ⟩ := hs
  refine ⟨rfl, ?_⟩
  filter_upwards [hU.mem_nhds hy] with y' hy'
  exact ⟨(hγ y' hy').differentiableAt, adb_mem_mcPts_iff.2 (hpts y' hy'), hΨ y' hy'⟩

theorem IsSheetParamB.eventuallyEq (hs : IsSheetParamB P Ψ U γ) {y : Fin D → ℂ} (hy : y ∈ U)
    {γ' : (Fin D → ℂ) → Ix κ → ℂ} (h' : IsSheet P Ψ y (segre (ι := GlobalTheory κ) (γ y)) γ') :
    γ' =ᶠ[𝓝 y] γ := by
  obtain ⟨hseg, hev⟩ := h'
  have hγy : γ' y = γ y := adb_segre_injective hseg
  obtain ⟨⟨hU, hγ, hpts, O, q, hO, hq, hOpts, hOc, hqγ⟩, hΨ⟩ := hs
  have hγO : γ y ∈ O := by
    have : γ y ∈ O ∩ pts P := by rw [hOpts]; exact adb_mem_coneOver_self hy
    exact this.1
  have hcont : ContinuousAt γ' y := hev.self_of_nhds.1.continuousAt
  have hO' : ∀ᶠ y' in 𝓝 y, γ' y' ∈ O := by
    apply hcont.preimage_mem_nhds
    rw [hγy]
    exact hO.mem_nhds hγO
  filter_upwards [hev, hO'] with y' ⟨_, hmc, hΨ'⟩ hy'O
  have hmem : γ' y' ∈ coneOver U γ := by
    rw [← hOpts]
    exact ⟨hy'O, adb_mem_mcPts_iff.1 hmc⟩
  exact (IsSheetParamB.eq_of_mem ⟨⟨hU, hγ, hpts, O, q, hO, hq, hOpts, hOc, hqγ⟩, hΨ⟩ hmem hΨ').2

theorem IsSheetParamB.sheetDensity_eq (hs : IsSheetParamB P Ψ U γ) {y : Fin D → ℂ} (hy : y ∈ U)
    (φ : Fin D → (Ix κ → ℂ) → ℝ) (h : (Ix κ → ℂ) → ℝ) :
    sheetDensity P Ψ φ h y (segre (ι := GlobalTheory κ) (γ y)) =
      h (γ y) * maDensity (fun j y' => φ j (γ y')) y := by
  have hex : ∃ γ'', IsSheet P Ψ y (segre (ι := GlobalTheory κ) (γ y)) γ'' := ⟨γ, hs.isSheet hy⟩
  simp only [sheetDensity, dif_pos hex]
  have heq := hs.eventuallyEq hy hex.choose_spec
  have hpt : hex.choose y = γ y := heq.self_of_nhds
  rw [hpt]
  congr 1
  unfold maDensity
  congr 4
  funext k
  unfold cxHessian
  have hf : (fun y' => φ k (hex.choose y')) =ᶠ[𝓝 y] fun y' => φ k (γ y') :=
    heq.fun_comp (φ k)
  rw [hf.fderiv.fderiv_eq]

theorem adb_measurable_cxHessian (f : (Fin D → ℂ) → ℝ) (i j : Fin D) :
    Measurable fun y => cxHessian f y i j := by
  have hH := measurable_fderiv ℝ (fderiv ℝ f)
  have hap : ∀ a b : Fin D → ℂ, Measurable fun y => fderiv ℝ (fderiv ℝ f) y a b := fun a b =>
    ((ContinuousLinearMap.apply ℝ ℝ b).continuous.comp
      (ContinuousLinearMap.apply ℝ _ a).continuous).measurable.comp hH
  simp only [cxHessian]
  exact (((Complex.measurable_ofReal.comp ((hap _ _).add (hap _ _))).add
    (measurable_const.mul (Complex.measurable_ofReal.comp ((hap _ _).sub (hap _ _))))).div_const 4)

theorem adb_continuous_mixedDisc :
    Continuous (mixedDisc : (Fin D → Matrix (Fin D) (Fin D) ℂ) → ℂ) := by
  unfold mixedDisc
  exact continuous_const.mul (continuous_finset_sum _ fun S _ => continuous_const.mul
    ((continuous_finset_sum _ fun k _ => continuous_apply k).matrix_det))

theorem adb_measurable_maDensity (φ : Fin D → (Fin D → ℂ) → ℝ) : Measurable (maDensity φ) := by
  have hcx : ∀ k i j, Measurable fun z => cxHessian (φ k) z i j := fun k i j =>
    adb_measurable_cxHessian (φ k) i j
  unfold maDensity mixedDisc
  simp only [Matrix.det_apply, Matrix.sum_apply]
  refine measurable_const.mul (Complex.measurable_re.comp (measurable_const.mul
    (Finset.measurable_sum _ fun S _ => measurable_const.mul
      (Finset.measurable_sum _ fun σ _ => (Finset.measurable_prod _ fun i _ =>
        Finset.measurable_sum _ fun k _ => hcx k _ _).const_smul _))))

def IsConeSetB (s : Set (Ix κ → ℂ)) : Prop :=
  ∀ (c : ℂ) (z : Ix κ → ℂ), c ≠ 0 → (c • z ∈ s ↔ z ∈ s)

theorem isConeSetB_coneOver (U : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → Ix κ → ℂ) :
    IsConeSetB (coneOver U γ) := by
  intro c z hc
  constructor
  · rintro ⟨y, hy, c', hc', hz⟩
    refine ⟨y, hy, c⁻¹ * c', mul_ne_zero (inv_ne_zero hc) hc', ?_⟩
    rw [mul_smul, ← hz, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · rintro ⟨y, hy, c', hc', rfl⟩
    exact ⟨y, hy, c * c', mul_ne_zero hc hc', by rw [mul_smul]⟩

theorem IsConeSetB.inter {s t : Set (Ix κ → ℂ)} (hs : IsConeSetB s) (ht : IsConeSetB t) :
    IsConeSetB (s ∩ t) := fun c z hc => by
  simp only [Set.mem_inter_iff, hs c z hc, ht c z hc]

theorem IsConeSetB.compl {s : Set (Ix κ → ℂ)} (hs : IsConeSetB s) : IsConeSetB sᶜ := fun c z hc => by
  simp only [Set.mem_compl_iff, hs c z hc]

theorem IsConeSetB.iInter {ι : Sort*} {s : ι → Set (Ix κ → ℂ)} (hs : ∀ i, IsConeSetB (s i)) :
    IsConeSetB (⋂ i, s i) := fun c z hc => by
  simp only [Set.mem_iInter]
  exact forall_congr' fun i => hs i c z hc

theorem IsConeSetB.disjointed {s : ℕ → Set (Ix κ → ℂ)} (hs : ∀ i, IsConeSetB (s i)) (n : ℕ) :
    IsConeSetB (disjointed s n) := by
  rw [disjointed_eq_inter_compl]
  exact (hs n).inter (IsConeSetB.iInter fun i => IsConeSetB.iInter fun _ => (hs i).compl)

theorem IsConeSetB.indicator {s : Set (Ix κ → ℂ)} (hs : IsConeSetB s) {f : (Ix κ → ℂ) → ℝ}
    (hf : IsDegZero f) : IsDegZero (s.indicator f) := fun c z hc => by
  show s.indicator f (c • z) = s.indicator f z
  by_cases h : z ∈ s
  · rw [Set.indicator_of_mem ((hs c z hc).2 h), Set.indicator_of_mem h, hf c z hc]
  · rw [Set.indicator_of_notMem (fun h' => h ((hs c z hc).1 h')), Set.indicator_of_notMem h]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
