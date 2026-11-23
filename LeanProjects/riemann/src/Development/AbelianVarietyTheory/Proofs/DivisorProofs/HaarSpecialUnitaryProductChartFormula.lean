import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnRmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfC

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.FibreVol

theorem volume_box (ι κ : Type) [Fintype ι] [Fintype κ] :
    volume {θ : ι → κ → ℝ | ∀ i k, θ i k ∈ Set.Ioc (-Real.pi) Real.pi} =
      ENNReal.ofReal ((2 * Real.pi) ^ (Fintype.card κ * Fintype.card ι)) := by
  have e : {θ : ι → κ → ℝ | ∀ i k, θ i k ∈ Set.Ioc (-Real.pi) Real.pi} =
      Set.univ.pi fun _ : ι => Set.univ.pi fun _ : κ => Set.Ioc (-Real.pi) Real.pi := by
    ext θ; simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  rw [e, volume_pi_pi]
  simp only [volume_pi_pi, Real.volume_Ioc, Finset.prod_const, Finset.card_univ]
  rw [ENNReal.ofReal_pow (by positivity), pow_mul, show Real.pi - -Real.pi = 2 * Real.pi by ring]

theorem exists_measurable_extend {α β : Type} [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α]
    [BorelSpace α] [TopologicalSpace β] [T2Space β] [MeasurableSpace β] [BorelSpace β] (M : α → β) (s : Set α)
    (hs : MeasurableSet s) (hM : ContinuousOn M s) (hinj : Set.InjOn M s) (ψ : α → ℝ≥0∞) (hψ : Measurable ψ) :
    ∃ φ : β → ℝ≥0∞, Measurable φ ∧ (∀ a ∈ s, φ (M a) = ψ a) ∧ ∀ y, y ∉ M '' s → φ y = 0 := by
  classical
  let φ : β → ℝ≥0∞ := fun y => if h : ∃ a ∈ s, M a = y then ψ h.choose else 0
  have hφs : ∀ a ∈ s, φ (M a) = ψ a := by
    intro a ha
    have h : ∃ a' ∈ s, M a' = M a := ⟨a, ha, rfl⟩
    simp only [φ, dif_pos h]
    rw [hinj h.choose_spec.1 ha h.choose_spec.2]
  have hφ0 : ∀ y, y ∉ M '' s → φ y = 0 := by
    intro y hy
    have h : ¬ ∃ a ∈ s, M a = y := fun ⟨a, ha, e⟩ => hy ⟨a, ha, e⟩
    simp only [φ, dif_neg h]
  refine ⟨φ, fun t ht => ?_, hφs, hφ0⟩
  have e : φ ⁻¹' t = M '' (s ∩ ψ ⁻¹' t) ∪ {y | y ∉ M '' s ∧ (0 : ℝ≥0∞) ∈ t} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
    by_cases hy : y ∈ M '' s
    · obtain ⟨a, ha, rfl⟩ := hy
      rw [hφs a ha]
      constructor
      · intro h; exact Or.inl ⟨a, ⟨ha, h⟩, rfl⟩
      · rintro (⟨a', ⟨ha', h⟩, e⟩ | ⟨h, -⟩)
        · rwa [← hinj ha' ha e]
        · exact absurd ⟨a, ha, rfl⟩ h
    · rw [hφ0 y hy]
      constructor
      · intro h; exact Or.inr ⟨hy, h⟩
      · rintro (⟨a', ⟨ha', -⟩, e⟩ | ⟨-, h⟩)
        · exact absurd ⟨a', ha', e⟩ hy
        · exact h
  rw [e]
  refine MeasurableSet.union ((hs.inter (hψ ht)).image_of_continuousOn_injOn
    (hM.mono Set.inter_subset_left) (hinj.mono Set.inter_subset_left)) ?_
  by_cases h0 : (0 : ℝ≥0∞) ∈ t
  · have : {y | y ∉ M '' s ∧ (0 : ℝ≥0∞) ∈ t} = (M '' s)ᶜ := by ext y; simp [h0]
    rw [this]; exact (hs.image_of_continuousOn_injOn hM hinj).compl
  · have : {y | y ∉ M '' s ∧ (0 : ℝ≥0∞) ∈ t} = ∅ := by ext y; simp [h0]
    rw [this]; exact MeasurableSet.empty

open scoped Pointwise in
theorem haar_map_mul_right_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsHaarMeasure] (T : Subgroup G) (hT : IsCompact (T : Set G)) (g : G) (hg : g ∈ T) :
    ν.map (fun h => h * g) = ν := by
  have hm : ν.map (fun h => h * g) = Measure.modularCharacterFun g • ν := by
    rw [Measure.modularCharacterFun_eq_haarScalarFactor ν g]
    exact Measure.isMulLeftInvariant_eq_smul _ ν
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  set C : Set G := K * (T : Set G) with hC
  have hCc : IsCompact C := hK.mul hT
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  have hC1 : C ∈ 𝓝 (1 : G) := by
    refine Filter.mem_of_superset hK1 fun k hk => ?_
    exact ⟨k, hk, 1, T.one_mem, mul_one k⟩
  have hpos : ν C ≠ 0 := (ν.measure_pos_of_mem_nhds hC1).ne'
  have hfin : ν C ≠ ⊤ := hCc.measure_lt_top.ne
  have hpre : (fun h => h * g) ⁻¹' C = C := by
    ext h
    simp only [Set.mem_preimage, hC, Set.mem_mul]
    constructor
    · rintro ⟨k, hk, u, hu, e⟩
      exact ⟨k, hk, u * g⁻¹, T.mul_mem hu (T.inv_mem hg), by rw [← mul_assoc, e, mul_inv_cancel_right]⟩
    · rintro ⟨k, hk, u, hu, e⟩
      exact ⟨k, hk, u * g, T.mul_mem hu hg, by rw [← mul_assoc, e]⟩
  have h1 := congrArg (fun μ : Measure G => μ C) hm
  rw [Measure.map_apply (measurable_mul_const g) hCm, hpre, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul] at h1
  have hΔ : ((Measure.modularCharacterFun g : NNReal) : ℝ≥0∞) = 1 := by
    have h2 : (1 : ℝ≥0∞) * ν C = ((Measure.modularCharacterFun g : NNReal) : ℝ≥0∞) * ν C := by
      rw [one_mul]; exact h1
    first
    | exact ((ENNReal.mul_eq_mul_right hpos hfin).1 h2).symm
    | exact ((ENNReal.mul_left_inj hpos hfin).1 h2).symm
    | exact (ENNReal.mul_right_cancel hpos hfin h2).symm
  have hΔ' : Measure.modularCharacterFun g = 1 := by exact_mod_cast hΔ
  rw [hm, hΔ', one_smul]

theorem lintegral_box_translate (ι κ : Type) [Fintype ι] [Fintype κ] (f : (ι → κ → ℝ) → ℝ≥0∞)
    (hf : Measurable f)
    (hper : ∀ θ θ' : ι → κ → ℝ, (∀ i k, ∃ n : ℤ, θ' i k = θ i k + 2 * Real.pi * n) → f θ' = f θ)
    (θ0 : ι → κ → ℝ) :
    ∫⁻ θ in {θ : ι → κ → ℝ | ∀ i k, θ i k ∈ Set.Ioc (-Real.pi) Real.pi}, f (θ0 + θ) =
      ∫⁻ θ in {θ : ι → κ → ℝ | ∀ i k, θ i k ∈ Set.Ioc (-Real.pi) Real.pi}, f θ := by
  haveI hp : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  let R : AddCircle (2 * Real.pi) → ℝ := fun u => (AddCircle.measurableEquivIoc (2 * Real.pi) (-Real.pi) u : ℝ)
  have hR : Measurable R := measurable_subtype_coe.comp (AddCircle.measurableEquivIoc _ _).measurable
  have hRθ : ∀ θ : ℝ, ∃ n : ℤ, R θ = θ + 2 * Real.pi * n := by
    intro θ
    refine ⟨-toIocDiv hp.out (-Real.pi) θ, ?_⟩
    have h1 : R θ = toIocMod hp.out (-Real.pi) θ := by
      simp [R, AddCircle.measurableEquivIoc, AddCircle.equivIoc]
    have h2 := toIocMod_add_toIocDiv_zsmul hp.out (-Real.pi) θ
    rw [zsmul_eq_mul] at h2
    rw [h1]; push_cast; linarith
  let e : (ι → κ → ℝ) → (ι → κ → AddCircle (2 * Real.pi)) := fun θ i k => (θ i k : AddCircle (2 * Real.pi))
  let g : (ι → κ → AddCircle (2 * Real.pi)) → ℝ≥0∞ := fun u => f fun i k => R (u i k)
  have hg : Measurable g := hf.comp (measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun k =>
    hR.comp ((measurable_pi_apply k).comp (measurable_pi_apply i)))
  have hge : ∀ θ, g (e θ) = f θ := fun θ => hper _ _ fun i k => hRθ (θ i k)
  have hbox : {θ : ι → κ → ℝ | ∀ i k, θ i k ∈ Set.Ioc (-Real.pi) Real.pi} =
      Set.univ.pi fun _ : ι => Set.univ.pi fun _ : κ => Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
    ext θ; simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  have hmeas : (volume : Measure (ι → κ → ℝ)).restrict
      {θ : ι → κ → ℝ | ∀ i k, θ i k ∈ Set.Ioc (-Real.pi) Real.pi} =
      Measure.pi fun _ : ι => Measure.pi fun _ : κ =>
        (volume : Measure ℝ).restrict (Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)) := by
    rw [hbox, volume_pi, Measure.restrict_pi_pi]
    congr 1; funext i
    rw [volume_pi, Measure.restrict_pi_pi]
  have hmp : MeasurePreserving e ((volume : Measure (ι → κ → ℝ)).restrict
      {θ : ι → κ → ℝ | ∀ i k, θ i k ∈ Set.Ioc (-Real.pi) Real.pi}) volume := by
    rw [hmeas, volume_pi]
    refine measurePreserving_pi (fun _ : ι => Measure.pi fun _ : κ =>
        (volume : Measure ℝ).restrict (Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)))
      (fun _ : ι => (volume : Measure (κ → AddCircle (2 * Real.pi))))
      (f := fun _ a k => (a k : AddCircle (2 * Real.pi))) fun i => ?_
    rw [volume_pi]
    exact measurePreserving_pi (fun _ : κ => (volume : Measure ℝ).restrict (Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)))
      (fun _ : κ => (volume : Measure (AddCircle (2 * Real.pi))))
      (f := fun _ (y : ℝ) => (y : AddCircle (2 * Real.pi)))
      fun k => AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi)
  have hadd : ∀ θ, e (θ0 + θ) = e θ0 + e θ := by
    intro θ; funext i k; simp [e]
  calc ∫⁻ θ in {θ : ι → κ → ℝ | ∀ i k, θ i k ∈ Set.Ioc (-Real.pi) Real.pi}, f (θ0 + θ)
      = ∫⁻ θ in {θ : ι → κ → ℝ | ∀ i k, θ i k ∈ Set.Ioc (-Real.pi) Real.pi}, (fun u => g (e θ0 + u)) (e θ) := by
        refine lintegral_congr fun θ => ?_
        simp only [← hadd, hge]
    _ = ∫⁻ u, g (e θ0 + u) := hmp.lintegral_comp (hg.comp (measurable_const_add _))
    _ = ∫⁻ u, g u := lintegral_add_left_eq_self g (e θ0)
    _ = ∫⁻ θ in {θ : ι → κ → ℝ | ∀ i k, θ i k ∈ Set.Ioc (-Real.pi) Real.pi}, g (e θ) := (hmp.lintegral_comp hg).symm
    _ = _ := lintegral_congr fun θ => hge θ

set_option maxHeartbeats 800000 in

theorem haar_chart_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)] (ν : Measure (realSU X.Ψ X.Gm)) (σ : V (nd X) → realSU X.Ψ X.Gm) (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (ρ : ℝ), 1 ≤ r → IsOrth X x → ν.IsHaarMeasure → (∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) → ∫⁻ g, φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) ∂ν = ∫⁻ z, φ (cpt X x z) ∂muF X x) → 0 < ρ → ContinuousOn σ (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) → (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) → (∀ θ θ', t (θ + θ') = t θ * t θ') → Continuous t → (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) → ∀ A : Set (ChartSp X), MeasurableSet A → A ⊆ Metric.ball 0 (min ρ Real.pi) → ν ((fun w : ChartSp X => σ w.1 * t w.2) '' A) = ∫⁻ w in A, ENNReal.ofReal (densF X x w.1 / (2 * Real.pi) ^ ((r - 1) * X.Ψ.card)) ∂(volume : Measure (ChartSp X)) := by
  intro E _ _ _ r X x _ _ ν σ t ρ hr hx hν hH hρ hσc hσ ht tadd tc hstab A hA hAsub
  classical
  let L : realSU X.Ψ X.Gm → Frame X.Ψ r → Frame X.Ψ r := fun g y =>
    X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) y
  change ∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, L (σ z) x = rmul (cpt X x z) b at hσ
  change ∀ θ, L (t θ) x = rmul x (phaseFrame θ) at ht
  change ∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, L g x = rmul x b) → ∃ θ, g = t θ at hstab
  change ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) →
    ∫⁻ g, φ (L g x) ∂ν = ∫⁻ z, φ (cpt X x z) ∂muF X x at hH

  have hLmul : ∀ g h y, L (g * h) y = L g (L h y) := by
    intro g h y
    funext τ
    show ((((g : X.Ψ → GL (Fin r) ℂ) τ * (h : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) :
      Matrix (Fin r) (Fin r) ℂ) * mat y τ : Matrix (Fin r) (Fin r) ℂ) =
      ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) *
        (((h : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * mat y τ)
    rw [Units.val_mul, Matrix.mul_assoc]
  have hL1 : ∀ y, L 1 y = y := by
    intro y; funext τ
    show (((1 : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat y τ = y τ
    simp [mat]; rfl
  have hLr : ∀ g y b, L g (rmul y b) = rmul (L g y) b := fun g y b =>
    GlobalTheory.UnitaryInvMeasure.lmulC_rmul X _ y b
  have hxu : ∀ τ, IsUnit (mat x τ).det := fun τ => isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X hx τ)
  have hLinj : ∀ g h, L g x = L h x → g = h := by
    intro g h e
    apply Subtype.ext
    funext τ
    apply Units.ext
    have e1 : ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * mat x τ =
        ((h : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * mat x τ := congrFun e τ
    have e2 := congrArg (fun M => M * (mat x τ)⁻¹) e1
    simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ (hxu τ)] using e2
  have hrx : ∀ p p' : Frame X.Ψ r, rmul x p = rmul x p' → p = p' := by
    intro p p' e
    funext τ
    have e1 : mat x τ * mat p τ = mat x τ * mat p' τ := congrFun e τ
    have e2 := congrArg (fun M => (mat x τ)⁻¹ * M) e1
    have e3 : mat p τ = mat p' τ := by simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ (hxu τ)] using e2
    exact e3
  have hU : ∀ g : realSU X.Ψ X.Gm, X.IsUnitaryC fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) :=
    fun g τ u w => (g.2 τ).2 u w

  have hphB : ∀ θ, phaseFrame (E := E) (Ψ := X.Ψ) (r := r) θ ∈ Bor X.Ψ r := by
    intro θ τ
    refine ⟨?_, fun a c hca => ?_⟩
    · show (Matrix.diagonal fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ))).det ≠ 0
      rw [Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun a _ => Complex.exp_ne_zero _
    · show (Matrix.diagonal fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ))) a c = 0
      exact Matrix.diagonal_apply_ne _ (ne_of_gt hca)
  have hang : ∀ (θ θ' : X.Ψ → Fin (r - 1) → ℝ), (∀ i k, ∃ n : ℤ, θ' i k = θ i k + 2 * Real.pi * n) →
      ∀ τ a, ∃ m : ℤ, angles (θ' τ) a = angles (θ τ) a + 2 * Real.pi * m := by
    intro θ θ' hn τ a
    choose n hn using hn
    unfold angles
    split_ifs with h
    · exact ⟨n τ ⟨a, h⟩, hn τ ⟨a, h⟩⟩
    · refine ⟨-∑ k, n τ k, ?_⟩
      simp only [hn τ, Finset.sum_add_distrib, ← Finset.mul_sum]
      push_cast
      ring
  have hph_per : ∀ (θ θ' : X.Ψ → Fin (r - 1) → ℝ), (∀ i k, ∃ n : ℤ, θ' i k = θ i k + 2 * Real.pi * n) →
      phaseFrame (E := E) (Ψ := X.Ψ) (r := r) θ' = phaseFrame θ := by
    intro θ θ' hn
    funext τ
    show (Matrix.diagonal fun a => Complex.exp (Complex.I * (angles (θ' τ) a : ℂ))) =
      Matrix.diagonal fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ))
    congr 1
    funext a
    obtain ⟨m, hm⟩ := hang θ θ' hn τ a
    rw [hm, Complex.exp_eq_exp_iff_exists_int]
    exact ⟨m, by push_cast; ring⟩
  have ht_per : ∀ (θ θ' : X.Ψ → Fin (r - 1) → ℝ), (∀ i k, ∃ n : ℤ, θ' i k = θ i k + 2 * Real.pi * n) →
      t θ' = t θ := by
    intro θ θ' hn
    apply hLinj
    rw [ht, ht, hph_per θ θ' hn]
  have hph_inj : ∀ (θ θ' : X.Ψ → Fin (r - 1) → ℝ), (∀ i k, θ i k ∈ Set.Ioc (-Real.pi) Real.pi) →
      (∀ i k, |θ' i k| < Real.pi) → phaseFrame (E := E) (Ψ := X.Ψ) (r := r) θ = phaseFrame θ' → θ = θ' := by
    intro θ θ' h1 h2 e
    funext τ k
    have hk : (k : ℕ) < r := lt_of_lt_of_le k.isLt (Nat.sub_le r 1)
    have e1 := congrFun (congrFun (congrFun e τ) ⟨k, hk⟩) ⟨k, hk⟩
    simp only [phaseFrame, Matrix.diagonal_apply_eq, angles, k.isLt, dif_pos] at e1
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp e1
    have hn' : θ τ k = θ' τ k + n * (2 * Real.pi) := by
      have := congrArg Complex.im hn
      simp at this
      linarith
    have hpi := Real.pi_pos
    have a1 := (h1 τ k).1
    have a2 := (h1 τ k).2
    have b := abs_lt.mp (h2 τ k)
    have hn1 : (n : ℝ) < 1 := by nlinarith
    have hn2 : (-1 : ℝ) < n := by nlinarith
    have : n = 0 := by
      have := Int.cast_lt.mp (by simpa using hn1 : (n : ℝ) < ((1 : ℤ) : ℝ))
      have := Int.cast_lt.mp (by simpa using hn2 : ((-1 : ℤ) : ℝ) < (n : ℝ))
      omega
    rw [hn', this]; simp

  have hflag : ∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∀ θ, ∃ b ∈ Bor X.Ψ r,
      L (σ z * t θ) x = rmul (cpt X x z) b := by
    intro z hz θ
    obtain ⟨b, hb, e⟩ := hσ z hz
    refine ⟨rmul b (phaseFrame θ), ExtFPf.mul_mem X hb (hphB θ), ?_⟩
    rw [hLmul, ht, hLr, e, ExtFPf.rmul_assoc]
  have hcoinc : ∀ z z' θ θ', z ∈ Metric.ball (0 : V (nd X)) ρ → z' ∈ Metric.ball (0 : V (nd X)) ρ →
      σ z * t θ = σ z' * t θ' → z = z' ∧ phaseFrame (E := E) (Ψ := X.Ψ) (r := r) θ = phaseFrame θ' := by
    intro z z' θ θ' hz hz' e
    obtain ⟨b, hb, eb⟩ := hflag z hz θ
    obtain ⟨b', hb', eb'⟩ := hflag z' hz' θ'
    have hzz : z = z' := (KU.cpt_inj X hx hb hb' (by rw [← eb, ← eb', e])).1
    subst hzz
    refine ⟨rfl, ?_⟩
    have e2 : t θ = t θ' := mul_left_cancel e
    apply hrx
    rw [← ht, ← ht, e2]

  have hball : ∀ w ∈ Metric.ball (0 : ChartSp X) (min ρ Real.pi),
      w.1 ∈ Metric.ball (0 : V (nd X)) ρ ∧ ∀ i k, |w.2 i k| < Real.pi := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    have h1 : ‖w‖ < ρ := lt_of_lt_of_le hw (min_le_left _ _)
    have h2 : ‖w‖ < Real.pi := lt_of_lt_of_le hw (min_le_right _ _)
    refine ⟨by rw [Metric.mem_ball, dist_zero_right]; exact lt_of_le_of_lt (norm_fst_le w) h1, fun i k => ?_⟩
    rw [← Real.norm_eq_abs]
    exact lt_of_le_of_lt ((norm_le_pi_norm (w.2 i) k).trans ((norm_le_pi_norm w.2 i).trans (norm_snd_le w))) h2
  set Q : ChartSp X → realSU X.Ψ X.Gm := fun w => σ w.1 * t w.2 with hQ
  set box : Set (X.Ψ → Fin (r - 1) → ℝ) := {θ | ∀ i k, θ i k ∈ Set.Ioc (-Real.pi) Real.pi} with hbox
  have hinj : Set.InjOn Q (Metric.ball 0 (min ρ Real.pi)) := by
    intro w hw w' hw' e
    obtain ⟨h1, h2⟩ := hball w hw
    obtain ⟨h1', h2'⟩ := hball w' hw'
    obtain ⟨hz, hp⟩ := hcoinc _ _ _ _ h1 h1' e
    refine Prod.ext hz (hph_inj _ _ (fun i k => ?_) h2' hp)
    exact ⟨(abs_lt.mp (h2 i k)).1, (abs_lt.mp (h2 i k)).2.le⟩
  have hQc : ContinuousOn Q (Metric.ball 0 (min ρ Real.pi)) := by
    refine ContinuousOn.mul ?_ (tc.comp continuous_snd).continuousOn
    exact hσc.comp continuousOn_fst fun w hw => (hball w hw).1
  have hS : MeasurableSet (Q '' A) :=
    hA.image_of_continuousOn_injOn (hQc.mono hAsub) (hinj.mono hAsub)

  have ht0 : t 0 = 1 := mul_left_cancel (a := t 0) (by rw [mul_one, ← tadd, add_zero])
  let T : Subgroup (realSU X.Ψ X.Gm) :=
    { carrier := Set.range t
      mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, tadd a b⟩
      one_mem' := ⟨0, ht0⟩
      inv_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨-a, by rw [eq_inv_iff_mul_eq_one, ← tadd, neg_add_cancel, ht0]⟩ }
  have hTc : IsCompact (T : Set (realSU X.Ψ X.Gm)) := by
    have hK : IsCompact {θ : X.Ψ → Fin (r - 1) → ℝ | ∀ i k, θ i k ∈ Set.Icc (-Real.pi) Real.pi} := by
      have e : {θ : X.Ψ → Fin (r - 1) → ℝ | ∀ i k, θ i k ∈ Set.Icc (-Real.pi) Real.pi} =
          Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Icc (-Real.pi) Real.pi := by
        ext θ; simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
      rw [e]; exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
    have e : (T : Set (realSU X.Ψ X.Gm)) =
        t '' {θ : X.Ψ → Fin (r - 1) → ℝ | ∀ i k, θ i k ∈ Set.Icc (-Real.pi) Real.pi} := by
      apply le_antisymm
      · rintro _ ⟨θ, rfl⟩
        refine ⟨fun i k => toIocMod Real.two_pi_pos (-Real.pi) (θ i k), fun i k => ?_, ?_⟩
        · have := toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) (θ i k)
          rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at this
          exact Set.Ioc_subset_Icc_self this
        · refine ht_per _ _ fun i k => ⟨-toIocDiv Real.two_pi_pos (-Real.pi) (θ i k), ?_⟩
          have := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (-Real.pi) (θ i k)
          rw [zsmul_eq_mul] at this
          beta_reduce
          push_cast
          linarith
      · rintro _ ⟨θ, -, rfl⟩; exact ⟨θ, rfl⟩
    rw [e]; exact hK.image tc
  have hνr : ∀ θ, ν.map (fun h => h * t θ) = ν := fun θ =>
    haar_map_mul_right_of_compact ν T hTc (t θ) ⟨θ, rfl⟩

  have hboxm : MeasurableSet box := by
    have e : box = ⋂ i, ⋂ k, (fun θ : X.Ψ → Fin (r - 1) → ℝ => θ i k) ⁻¹' Set.Ioc (-Real.pi) Real.pi := by
      ext θ; simp [hbox]
    rw [e]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun k =>
      measurableSet_Ioc.preimage ((measurable_pi_apply k).comp (measurable_pi_apply i))
  set c : ℝ := (2 * Real.pi) ^ ((r - 1) * X.Ψ.card) with hc
  have hcpos : 0 < c := pow_pos Real.two_pi_pos _
  have hvol : volume box = ENNReal.ofReal c := by
    rw [hbox, volume_box]
    simp [hc, Fintype.card_coe]

  set S := Q '' A with hSdef
  have hI1 : Measurable fun p : realSU X.Ψ X.Gm × (X.Ψ → Fin (r - 1) → ℝ) => S.indicator (1 : realSU X.Ψ X.Gm → ℝ≥0∞) (p.1 * t p.2) :=
    (measurable_one.indicator hS).comp (continuous_fst.mul (tc.comp continuous_snd)).measurable
  have step1 : ∫⁻ g, (∫⁻ θ in box, S.indicator (1 : realSU X.Ψ X.Gm → ℝ≥0∞) (g * t θ)) ∂ν = ν S * ENNReal.ofReal c := by
    rw [lintegral_lintegral_swap (f := fun g θ => S.indicator (1 : realSU X.Ψ X.Gm → ℝ≥0∞) (g * t θ)) hI1.aemeasurable]
    have : ∀ θ, ∫⁻ g, S.indicator (1 : realSU X.Ψ X.Gm → ℝ≥0∞) (g * t θ) ∂ν = ν S := by
      intro θ
      rw [← lintegral_map (measurable_one.indicator hS) (measurable_mul_const (t θ)), hνr θ,
        lintegral_indicator_one hS]
    simp only [this, lintegral_const, Measure.restrict_apply_univ, hvol]

  set ψ0 : V (nd X) → ℝ≥0∞ := fun z => ∫⁻ θ in box, A.indicator (1 : ChartSp X → ℝ≥0∞) (z, θ) with hψ0
  have hAind : Measurable (A.indicator (1 : ChartSp X → ℝ≥0∞)) := measurable_one.indicator hA
  have hψ0m : Measurable ψ0 := hAind.lintegral_prod_right'
  have hBorm : MeasurableSet (Bor X.Ψ r) := by
    have e : Bor X.Ψ r = ⋂ τ : X.Ψ, ({b : Frame X.Ψ r | (mat b τ).det ≠ 0} ∩
        ⋂ a : Fin r, ⋂ c : Fin r, {b : Frame X.Ψ r | c < a → b τ a c = 0}) := by
      ext b; simp [Bor]
    rw [e]
    refine MeasurableSet.iInter fun τ => MeasurableSet.inter ?_
      (MeasurableSet.iInter fun a => MeasurableSet.iInter fun c => ?_)
    · have hc : Continuous fun b : Frame X.Ψ r => (mat b τ).det :=
        Continuous.matrix_det (show Continuous fun b : Frame X.Ψ r => mat b τ from continuous_apply τ)
      exact (isOpen_ne_fun hc continuous_const).measurableSet
    · by_cases h : c < a
      · have : {b : Frame X.Ψ r | c < a → b τ a c = 0} = {b | b τ a c = 0} := by ext b; simp [h]
        rw [this]
        exact (isClosed_eq ((continuous_apply c).comp ((continuous_apply a).comp (continuous_apply τ)))
          continuous_const).measurableSet
      · have : {b : Frame X.Ψ r | c < a → b τ a c = 0} = Set.univ := by ext b; simp [h]
        rw [this]; exact MeasurableSet.univ

  let M : V (nd X) × Frame X.Ψ r → Frame X.Ψ r := fun p => rmul (cpt X x p.1) p.2
  have hMc : Continuous M := (GlobalTheory.UnitaryInvMeasure.continuous_rmul X).comp
    (((KU.cont_cpt X x).comp continuous_fst).prodMk continuous_snd)
  have hMinj : Set.InjOn M (Metric.ball (0 : V (nd X)) ρ ×ˢ Bor X.Ψ r) := by
    rintro ⟨z, b⟩ ⟨-, hb⟩ ⟨z', b'⟩ ⟨-, hb'⟩ e
    obtain ⟨h1, h2⟩ := KU.cpt_inj X hx hb hb' e
    exact Prod.ext h1 h2
  haveI hPol : PolishSpace (Frame X.Ψ r) := by
    show PolishSpace (X.Ψ → Fin r → Fin r → ℂ)
    letI : NormedAddCommGroup (X.Ψ → Fin r → Fin r → ℂ) := inferInstance
    haveI : CompleteSpace (X.Ψ → Fin r → Fin r → ℂ) := inferInstance
    haveI : TopologicalSpace.SeparableSpace (X.Ψ → Fin r → Fin r → ℂ) := inferInstance
    infer_instance
  haveI hPol2 : PolishSpace (V (nd X) × Frame X.Ψ r) := by
    show PolishSpace (V (nd X) × (X.Ψ → Fin r → Fin r → ℂ))
    letI : NormedAddCommGroup (V (nd X) × (X.Ψ → Fin r → Fin r → ℂ)) := inferInstance
    haveI : CompleteSpace (V (nd X) × (X.Ψ → Fin r → Fin r → ℂ)) := inferInstance
    haveI : TopologicalSpace.SeparableSpace (V (nd X) × (X.Ψ → Fin r → Fin r → ℂ)) := inferInstance
    infer_instance
  obtain ⟨φ, hφm, hφM, hφ0⟩ := exists_measurable_extend M (Metric.ball (0 : V (nd X)) ρ ×ˢ Bor X.Ψ r)
    (measurableSet_ball.prod hBorm) hMc.continuousOn hMinj (fun p => ψ0 p.1) (hψ0m.comp measurable_fst)
  have hφB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y := by
    intro y _ b hb
    by_cases hy : y ∈ M '' (Metric.ball (0 : V (nd X)) ρ ×ˢ Bor X.Ψ r)
    · obtain ⟨⟨z, b0⟩, ⟨hz, hb0⟩, rfl⟩ := hy
      have e : rmul (M (z, b0)) b = M (z, rmul b0 b) := ExtFPf.rmul_assoc X _ _ _
      rw [e, hφM (z, rmul b0 b) ⟨hz, ExtFPf.mul_mem X hb0 hb⟩, hφM (z, b0) ⟨hz, hb0⟩]
    · have hy' : rmul y b ∉ M '' (Metric.ball (0 : V (nd X)) ρ ×ˢ Bor X.Ψ r) := by
        rintro ⟨⟨z, b1⟩, ⟨hz, hb1⟩, e⟩
        apply hy
        refine ⟨(z, rmul b1 (ExtFPf.invF X b)), ⟨hz, ExtFPf.mul_mem X hb1 (ExtFPf.invF_mem X hb)⟩, ?_⟩
        show rmul (cpt X x z) (rmul b1 (ExtFPf.invF X b)) = y
        rw [← ExtFPf.rmul_assoc, show rmul (cpt X x z) b1 = rmul y b from e, ExtFPf.rmul_assoc,
          ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]
      rw [hφ0 _ hy, hφ0 _ hy']

  have hper_f : ∀ z, Measurable (fun θ => S.indicator (1 : realSU X.Ψ X.Gm → ℝ≥0∞) (σ z * t θ)) := fun z =>
    (measurable_one.indicator hS).comp (continuous_const.mul tc).measurable
  have hslice : ∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∀ θ ∈ box,
      S.indicator (1 : realSU X.Ψ X.Gm → ℝ≥0∞) (σ z * t θ) = A.indicator (1 : ChartSp X → ℝ≥0∞) (z, θ) := by
    intro z hz θ hθ
    have hiff : σ z * t θ ∈ S ↔ (z, θ) ∈ A := by
      constructor
      · rintro ⟨⟨z', θ'⟩, hw, e⟩
        obtain ⟨h1, h2⟩ := hball _ (hAsub hw)
        obtain ⟨hzz, hp⟩ := hcoinc z' z θ' θ h1 hz e
        have hθθ : θ = θ' := hph_inj θ θ' hθ h2 hp.symm
        rw [← hzz, hθθ]; exact hw
      · intro h; exact ⟨(z, θ), h, rfl⟩
    by_cases h : (z, θ) ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.2 h)]; rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hiff.1 h'))]
  have hFφ : ∀ g, ∫⁻ θ in box, S.indicator (1 : realSU X.Ψ X.Gm → ℝ≥0∞) (g * t θ) = φ (L g x) := by
    intro g
    by_cases hg : L g x ∈ M '' (Metric.ball (0 : V (nd X)) ρ ×ˢ Bor X.Ψ r)
    · obtain ⟨⟨z, b⟩, ⟨hz, hb⟩, hzb⟩ := hg
      rw [← hzb, hφM (z, b) ⟨hz, hb⟩]
      obtain ⟨b1, hb1, e1⟩ := hσ z hz
      have ec : cpt X x z = rmul (L (σ z) x) (ExtFPf.invF X b1) := by
        rw [e1, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb1, ExtFPf.rmul_oneF]
      obtain ⟨θ0, hθ0⟩ := hstab ((σ z)⁻¹ * g) ⟨rmul (ExtFPf.invF X b1) b,
        ExtFPf.mul_mem X (ExtFPf.invF_mem X hb1) hb, by
          rw [hLmul, ← hzb]
          show L (σ z)⁻¹ (rmul (cpt X x z) b) = _
          rw [ec, hLr, hLr, ← hLmul, inv_mul_cancel, hL1, ExtFPf.rmul_assoc]⟩
      have hg' : g = σ z * t θ0 := by rw [← hθ0, mul_inv_cancel_left]
      subst hg'
      calc ∫⁻ θ in box, S.indicator (1 : realSU X.Ψ X.Gm → ℝ≥0∞) (σ z * t θ0 * t θ)
          = ∫⁻ θ in box, (fun θ => S.indicator (1 : realSU X.Ψ X.Gm → ℝ≥0∞) (σ z * t θ)) (θ0 + θ) := by
            simp only [tadd, mul_assoc]
        _ = ∫⁻ θ in box, S.indicator (1 : realSU X.Ψ X.Gm → ℝ≥0∞) (σ z * t θ) :=
            lintegral_box_translate X.Ψ (Fin (r - 1)) _ (hper_f z)
              (fun θ θ' h => by simp only [ht_per θ θ' h]) θ0
        _ = ∫⁻ θ in box, A.indicator (1 : ChartSp X → ℝ≥0∞) (z, θ) :=
            setLIntegral_congr_fun hboxm (fun θ hθ => hslice z hz θ hθ)
    · rw [hφ0 _ hg]
      have : ∀ θ, S.indicator (1 : realSU X.Ψ X.Gm → ℝ≥0∞) (g * t θ) = 0 := by
        intro θ
        refine Set.indicator_of_notMem (fun hm => hg ?_) _
        obtain ⟨⟨z', θ'⟩, hw, e⟩ := hm
        obtain ⟨h1, -⟩ := hball _ (hAsub hw)
        have eg : g = σ z' * t (θ' - θ) := by
          have e' : σ z' * t θ' = g * t θ := e
          have : t θ' = t (θ' - θ) * t θ := by rw [← tadd, sub_add_cancel]
          rw [this, ← mul_assoc] at e'
          exact (mul_right_cancel e').symm
        obtain ⟨b, hb, eb⟩ := hflag z' h1 (θ' - θ)
        exact ⟨(z', b), ⟨h1, hb⟩, by rw [eg]; exact eb.symm⟩
      simp [this]

  have hφc : Measurable fun z => φ (cpt X x z) := hφm.comp (KU.cont_cpt X x).measurable
  have hballO : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x := by
    intro z hz
    obtain ⟨b, hb, e⟩ := hσ z hz
    have ec : cpt X x z = rmul (L (σ z) x) (ExtFPf.invF X b) := by
      rw [e, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]
    show cpt X x z ∈ X.dom
    rw [ec]
    exact OntoS.dom_rmul X (IC.orth_mem_dom X (GlobalTheory.UnitaryInvMeasure.orth_lmulC X (hU (σ z)) hx))
      (ExtFPf.invF_mem X hb)
  have hφcpt : ∀ z, φ (cpt X x z) = (Metric.ball (0 : V (nd X)) ρ).indicator ψ0 z := by
    intro z
    by_cases hz : z ∈ Metric.ball (0 : V (nd X)) ρ
    · rw [Set.indicator_of_mem hz]
      have := hφM (z, ExtFPf.oneF X) ⟨hz, ExtFPf.oneF_mem X⟩
      simpa [M, ExtFPf.rmul_oneF] using this
    · rw [Set.indicator_of_notMem hz]
      refine hφ0 _ ?_
      rintro ⟨⟨z', b⟩, ⟨hz', hb⟩, e⟩
      have e' : rmul (cpt X x z') b = rmul (cpt X x z) (ExtFPf.oneF X) := by
        rw [ExtFPf.rmul_oneF]; exact e
      exact hz ((KU.cpt_inj X hx hb (ExtFPf.oneF_mem X) e').1 ▸ hz')
  have step2 : ν S * ENNReal.ofReal c =
      ∫⁻ z, ENNReal.ofReal (densF X x z) * (Metric.ball (0 : V (nd X)) ρ).indicator ψ0 z := by
    rw [← step1]
    simp only [hFφ]
    rw [hH φ hφm hφB, muF, lintegral_withDensity_eq_lintegral_mul _ (OntoC.measurable_densF X x) hφc]
    simp only [Pi.mul_apply, hφcpt]
    refine setLIntegral_eq_of_support_subset ?_
    intro z hz
    by_contra h
    apply hz
    have : z ∉ Metric.ball (0 : V (nd X)) ρ := fun h' => h (hballO h')
    simp [Set.indicator_of_notMem this]

  have hslice0 : ∀ z, ∫⁻ θ, A.indicator (1 : ChartSp X → ℝ≥0∞) (z, θ) =
      (Metric.ball (0 : V (nd X)) ρ).indicator ψ0 z := by
    intro z
    by_cases hz : z ∈ Metric.ball (0 : V (nd X)) ρ
    · rw [Set.indicator_of_mem hz]
      refine (setLIntegral_eq_of_support_subset ?_).symm
      intro θ hθ
      have hm : (z, θ) ∈ A := by
        by_contra h; exact hθ (Set.indicator_of_notMem h _)
      obtain ⟨-, h2⟩ := hball _ (hAsub hm)
      exact fun i k => ⟨(abs_lt.mp (h2 i k)).1, (abs_lt.mp (h2 i k)).2.le⟩
    · rw [Set.indicator_of_notMem hz]
      have : ∀ θ, A.indicator (1 : ChartSp X → ℝ≥0∞) (z, θ) = 0 := fun θ =>
        Set.indicator_of_notMem (fun hm => hz (hball (z, θ) (hAsub hm)).1) _
      simp [this]
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hcpos).ne'
  have step3 : ∫⁻ w in A, ENNReal.ofReal (densF X x w.1 / c) ∂(volume : Measure (ChartSp X)) =
      (ENNReal.ofReal c)⁻¹ *
        ∫⁻ z, ENNReal.ofReal (densF X x z) * (Metric.ball (0 : V (nd X)) ρ).indicator ψ0 z := by
    have e : ∀ w : ChartSp X, ENNReal.ofReal (densF X x w.1 / c) =
        (ENNReal.ofReal c)⁻¹ * ENNReal.ofReal (densF X x w.1) := by
      intro w; rw [ENNReal.ofReal_div_of_pos hcpos, div_eq_mul_inv, mul_comm]
    simp only [e]
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hc0)]
    congr 1
    have hfm : Measurable (A.indicator fun w : ChartSp X => ENNReal.ofReal (densF X x w.1)) :=
      ((OntoC.measurable_densF X x).comp measurable_fst).indicator hA
    rw [← lintegral_indicator hA, Measure.volume_eq_prod, lintegral_prod _ hfm.aemeasurable]
    refine lintegral_congr fun z => ?_
    rw [← hslice0 z, ← lintegral_const_mul (ENNReal.ofReal (densF X x z))
      (f := fun θ => A.indicator (1 : ChartSp X → ℝ≥0∞) (z, θ)) (hAind.comp measurable_prodMk_left)]
    refine lintegral_congr fun θ => ?_
    by_cases h : (z, θ) ∈ A
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  rw [step3, ← step2, mul_comm (ν S), ← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]

end GlobalTheory.FibreVol
