import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeFundamentalDomainVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageExpectedCountStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CoefTheta

section Series

variable {Ω Z V : Type} [MeasurableSpace Ω] [Countable Z]

lemma tsum_lint {Pr : Measure Ω} {s : Z → Ω → ℂ} (hm : ∀ z, Measurable (s z)) :
    ∫⁻ ω, ∑' z, ‖s z ω‖ₑ ∂Pr = ∑' z, ∫⁻ ω, ‖s z ω‖ₑ ∂Pr :=
  lintegral_tsum fun z => (hm z).enorm.aemeasurable

lemma term_lint_ne_top {Pr : Measure Ω} {s : Z → Ω → ℂ} (hm : ∀ z, Measurable (s z))
    (hfin : ∫⁻ ω, ∑' z, ‖s z ω‖ₑ ∂Pr ≠ ∞) (z : Z) : ∫⁻ ω, ‖s z ω‖ₑ ∂Pr ≠ ∞ :=
  ENNReal.ne_top_of_tsum_ne_top (by rwa [← tsum_lint hm]) z

lemma term_integrable {Pr : Measure Ω} {s : Z → Ω → ℂ} (hm : ∀ z, Measurable (s z))
    (hfin : ∫⁻ ω, ∑' z, ‖s z ω‖ₑ ∂Pr ≠ ∞) (z : Z) : Integrable (s z) Pr :=
  ⟨(hm z).aestronglyMeasurable, lt_top_iff_ne_top.mpr (term_lint_ne_top hm hfin z)⟩

lemma summable_integral_norm {Pr : Measure Ω} {s : Z → Ω → ℂ} (hm : ∀ z, Measurable (s z))
    (hfin : ∫⁻ ω, ∑' z, ‖s z ω‖ₑ ∂Pr ≠ ∞) : Summable fun z => ∫ ω, ‖s z ω‖ ∂Pr := by
  have h : (fun z => ∫ ω, ‖s z ω‖ ∂Pr) = fun z => (∫⁻ ω, ‖s z ω‖ₑ ∂Pr).toReal :=
    funext fun z => integral_norm_eq_lintegral_enorm (hm z).aestronglyMeasurable
  rw [h]
  exact ENNReal.summable_toReal (by rwa [← tsum_lint hm])

lemma summable_norm_integral {Pr : Measure Ω} {s : Z → Ω → ℂ} (hm : ∀ z, Measurable (s z))
    (hfin : ∫⁻ ω, ∑' z, ‖s z ω‖ₑ ∂Pr ≠ ∞) : Summable fun z => ‖∫ ω, s z ω ∂Pr‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_integral_le_integral_norm _)
    (summable_integral_norm hm hfin)

lemma integral_series {Pr : Measure Ω} {s : Z → Ω → ℂ} (hm : ∀ z, Measurable (s z))
    (hfin : ∫⁻ ω, ∑' z, ‖s z ω‖ₑ ∂Pr ≠ ∞) (c : Z → ℂ) (hc : ∀ z, ‖c z‖ = 1) :
    ∫ ω, ∑' z, c z * s z ω ∂Pr = ∑' z, c z * ∫ ω, s z ω ∂Pr := by
  have h := hasSum_integral_of_summable_integral_norm (μ := Pr)
    (F := fun z ω => c z * s z ω) (fun z => (term_integrable hm hfin z).const_mul _)
    (by simpa [hc] using summable_integral_norm hm hfin)
  simpa [integral_const_mul] using h.tsum_eq.symm

variable [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]

theorem fourier_series {Pr : Measure Ω} {s : Z → Ω → ℂ} (hm : ∀ z, Measurable (s z))
    (hfin : ∫⁻ ω, ∑' z, ‖s z ω‖ₑ ∂Pr ≠ ∞) {μ : Measure V} [IsFiniteMeasure μ]
    {u : Z → V → ℂ} (hu : ∀ z, Continuous (u z)) (hun : ∀ z x, ‖u z x‖ = 1)
    {v : V → ℂ} (hv : Continuous v) (hvn : ∀ x, ‖v x‖ = 1) (Sel : Set Z) (Vol : ℂ)
    (h1 : ∀ z ∈ Sel, ∫ x, u z x * v x ∂μ = Vol)
    (h0 : ∀ z ∉ Sel, (∫ x, u z x * v x ∂μ = 0) ∨ ∀ ω, s z ω = 0) :
    Integrable (fun x => (∫ ω, ∑' z, u z x * s z ω ∂Pr) * v x) μ ∧
      ∫ x, (∫ ω, ∑' z, u z x * s z ω ∂Pr) * v x ∂μ = Vol * ∑' z : Sel, ∫ ω, s z.1 ω ∂Pr := by
  set S : Z → ℂ := fun z => ∫ ω, s z ω ∂Pr with hS
  have hSs : Summable fun z => ‖S z‖ := summable_norm_integral hm hfin
  have hA : ∀ x, ∫ ω, ∑' z, u z x * s z ω ∂Pr = ∑' z, u z x * S z := fun x =>
    integral_series hm hfin (fun z => u z x) (fun z => hun z x)
  simp_rw [hA]
  have hnorm : ∀ z x, ‖u z x * S z‖ = ‖S z‖ := fun z x => by simp [hun]
  have hcont : Continuous fun x => ∑' z, u z x * S z :=
    continuous_tsum (fun z => (hu z).mul continuous_const) hSs (fun z x => (hnorm z x).le)
  have hint : Integrable (fun x => (∑' z, u z x * S z) * v x) μ := by
    refine Integrable.of_bound (hcont.mul hv).aestronglyMeasurable (∑' z, ‖S z‖)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, hvn, mul_one]
    exact tsum_of_norm_bounded hSs.hasSum fun z => (hnorm z x).le
  refine ⟨hint, ?_⟩
  have hterm : ∀ z, Integrable (fun x => u z x * S z * v x) μ := fun z =>
    Integrable.of_bound (((hu z).mul continuous_const).mul hv).aestronglyMeasurable ‖S z‖
      (Filter.Eventually.of_forall fun x => by rw [norm_mul, hvn, mul_one, hnorm])
  have hsum : Summable fun z => ∫ x, ‖u z x * S z * v x‖ ∂μ := by
    have : (fun z => ∫ x, ‖u z x * S z * v x‖ ∂μ) = fun z => μ.real Set.univ * ‖S z‖ := by
      funext z
      simp [hun, hvn]
    rw [this]
    exact hSs.mul_left _
  have h := (hasSum_integral_of_summable_integral_norm hterm hsum).tsum_eq
  have hsw : ∀ x, (∑' z, u z x * S z) * v x = ∑' z, u z x * S z * v x := fun x =>
    (tsum_mul_right).symm
  simp_rw [hsw]
  rw [← h]
  have hval : ∀ z, ∫ x, u z x * S z * v x ∂μ = Sel.indicator (fun z => Vol * S z) z := by
    intro z
    have e : ∫ x, u z x * S z * v x ∂μ = (∫ x, u z x * v x ∂μ) * S z := by
      rw [← integral_mul_const]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only []; ring)
    by_cases hz : z ∈ Sel
    · rw [e, h1 z hz, Set.indicator_of_mem hz]
    · rw [e, Set.indicator_of_notMem hz]
      rcases h0 z hz with h | h
      · rw [h, zero_mul]
      · have : S z = 0 := by simp [hS, h]
        rw [this, mul_zero]
  simp_rw [hval]
  rw [← tsum_subtype, tsum_mul_left]

theorem sum_selected {Pr : Measure Ω} {s : Z → Ω → ℂ} (hm : ∀ z, Measurable (s z))
    (hfin : ∫⁻ ω, ∑' z, ‖s z ω‖ₑ ∂Pr ≠ ∞) (hpos : ∀ z ω, s z ω = ((‖s z ω‖ : ℝ) : ℂ)) (Sel : Set Z) :
    ∑' z : Sel, ∫ ω, s z.1 ω ∂Pr = (((∫⁻ ω, ∑' z : Sel, ‖s z.1 ω‖ₑ ∂Pr).toReal : ℝ) : ℂ) := by
  have hS : ∀ z : Z, ∫ ω, s z ω ∂Pr = (((∫⁻ ω, ‖s z ω‖ₑ ∂Pr).toReal : ℝ) : ℂ) := by
    intro z
    rw [← integral_norm_eq_lintegral_enorm (hm z).aestronglyMeasurable, ← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => hpos z ω)
  simp_rw [hS]
  rw [lintegral_tsum (f := fun (z : Sel) ω => ‖s z.1 ω‖ₑ) fun z => (hm z.1).enorm.aemeasurable,
    ENNReal.tsum_toReal_eq (f := fun z : Sel => ∫⁻ ω, ‖s z.1 ω‖ₑ ∂Pr)
      fun z => term_lint_ne_top hm hfin z.1, Complex.ofReal_tsum]

end Series

section Concrete

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma quad_orth {R : Type} [CommRing R] (g C : Matrix ι ι R) (v : ι → R) :
    (g *ᵥ v) ⬝ᵥ (C *ᵥ (g *ᵥ v)) = v ⬝ᵥ ((gᵀ * C * g) *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v gᵀ,
    Matrix.vecMul_transpose]

lemma dot_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (B : Matrix ι ι R) (v : ι → R) :
    (fun j => f (v j)) ⬝ᵥ (B.map f *ᵥ fun j => f (v j)) = f (v ⬝ᵥ (B *ᵥ v)) := by
  rw [RingHom.map_dotProduct]
  congr 1
  funext i
  exact (RingHom.map_mulVec f B v i).symm

variable {F : Type} [Field F] [NumberField F]

def ph (ρ : InfinitePlace F → (F →+* ℝ)) (b : F) (x : InfinitePlace F → ℝ) : ℂ :=
  Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w b * x w : ℝ) : ℂ))

lemma ph_continuous (ρ : InfinitePlace F → (F →+* ℝ)) (b : F) : Continuous (ph ρ b) := by
  unfold ph
  fun_prop

lemma ph_mul (ρ : InfinitePlace F → (F →+* ℝ)) (b c : F) (x : InfinitePlace F → ℝ) :
    ph ρ b x * ph ρ c x = ph ρ (b + c) x := by
  unfold ph
  rw [← Complex.exp_add, ← mul_add, ← Complex.ofReal_add, ← Finset.sum_add_distrib]
  simp only [map_add, add_mul]

lemma ph_zero (ρ : InfinitePlace F → (F →+* ℝ)) (x : InfinitePlace F → ℝ) : ph ρ 0 x = 1 := by
  simp [ph]

lemma ph_neg (ρ : InfinitePlace F → (F →+* ℝ)) (b : F) (x : InfinitePlace F → ℝ) :
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w b * x w : ℝ) : ℂ)) = ph ρ (-b) x := by
  unfold ph
  congr 1
  simp only [map_neg, neg_mul, Finset.sum_neg_distrib, Complex.ofReal_neg, mul_neg]

lemma ph_norm (ρ : InfinitePlace F → (F →+* ℝ)) (b : F) (x : InfinitePlace F → ℝ) :
    ‖ph ρ b x‖ = 1 := by
  unfold ph
  have : (2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w b * x w : ℝ) : ℂ) =
      ((2 * Real.pi * ∑ w, ρ w b * x w : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma thTerm_shift {B : Matrix ι ι F} {ρ : InfinitePlace F → (F →+* ℝ)}
    (P : InfinitePlace F → Matrix ι ι ℝ) {gf : Matrix ι ι (A F)}
    {gi : InfinitePlace F → Matrix ι ι ℝ} (hO : IsOrth B ρ gf gi) (φ : (ι → A F) → ℂ)
    (x : InfinitePlace F → ℝ) (z : ι → F) :
    thTerm B ρ P gf gi φ (fun w => (x w : ℂ) + Complex.I) z =
      ph ρ (qf (1 / 2 : F) B z) x * thTerm B ρ P gf gi φ (fun _ => Complex.I) z := by
  have hQ : ∀ w, (gi w *ᵥ fun j => ρ w (z j)) ⬝ᵥ (B.map (ρ w) *ᵥ (gi w *ᵥ fun j => ρ w (z j))) =
      2 * ρ w (qf (1 / 2 : F) B z) := by
    intro w
    have h2 : ρ w (1 / 2 : F) = 1 / 2 := by
      rw [map_div₀, map_one, map_ofNat]
    rw [quad_orth, hO.2 w, dot_map]
    unfold qf
    rw [map_mul, h2]
    ring
  unfold thTerm gauss ph
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  rw [Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [hQ w]
  simp
  ring

lemma thTerm_nonneg (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (gf : Matrix ι ι (A F))
    (gi : InfinitePlace F → Matrix ι ι ℝ) (a : ℕ) (z : ι → F) :
    thTerm B ρ P gf gi (indL a) (fun _ => Complex.I) z =
      ((‖thTerm B ρ P gf gi (indL a) (fun _ => Complex.I) z‖ : ℝ) : ℂ) := by
  have key : ∃ r : ℝ, 0 ≤ r ∧ thTerm B ρ P gf gi (indL a) (fun _ => Complex.I) z = (r : ℂ) := by
    have hg : gauss B ρ P (fun _ => Complex.I) (fun w => gi w *ᵥ fun j => ρ w (z j)) =
        ((Real.exp (∑ w, -(Real.pi * ((gi w *ᵥ fun j => ρ w (z j)) ⬝ᵥ
          (P w *ᵥ (gi w *ᵥ fun j => ρ w (z j)))))) : ℝ) : ℂ) := by
      unfold gauss
      rw [Complex.ofReal_exp]
      congr 1
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp
    obtain ⟨E, hE, hg'⟩ : ∃ E : ℝ, 0 ≤ E ∧
        gauss B ρ P (fun _ => Complex.I) (fun w => gi w *ᵥ fun j => ρ w (z j)) = (E : ℂ) := by
      refine ⟨_, ?_, hg⟩
      exact (Real.exp_pos _).le
    unfold thTerm
    rw [hg']
    by_cases h : (gf *ᵥ fun j => algebraMap F (A F) (z j)) ∈ {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}
    · exact ⟨E, hE, by simp only [indL, Set.indicator_of_mem h, one_mul]⟩
    · exact ⟨0, le_rfl, by simp only [indL, Set.indicator_of_notMem h]; simp⟩
  obtain ⟨r, hr, e⟩ := key
  rw [e, Complex.norm_real, Real.norm_of_nonneg hr]

lemma thTerm_zero_le (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (gf : Matrix ι ι (A F))
    (gi : InfinitePlace F → Matrix ι ι ℝ) (a : ℕ) :
    ‖thTerm B ρ P gf gi (indL a) (fun _ => Complex.I) 0‖ₑ ≤ 1 := by
  have hz : (gf *ᵥ fun j => algebraMap F (A F) ((0 : ι → F) j)) = 0 := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  have hg : gauss B ρ P (fun _ => Complex.I) (fun w => gi w *ᵥ fun j => ρ w ((0 : ι → F) j)) = 1 := by
    have : ∀ w, (gi w *ᵥ fun j => ρ w ((0 : ι → F) j)) = 0 := by
      intro w
      funext i
      simp [Matrix.mulVec, dotProduct]
    simp only [gauss, this]
    simp
  unfold thTerm
  rw [hz, hg, mul_one]
  by_cases h : (0 : ι → A F) ∈ {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}
  · simp only [indL, Set.indicator_of_mem h]
    simp
  · simp only [indL, Set.indicator_of_notMem h]
    simp

lemma qf_adelic {B : Matrix ι ι F} {gf : Matrix ι ι (A F)} (hO : gfᵀ * Bf B * gf = Bf B) (z : ι → F) :
    qf (hf F) (Bf B) (gf *ᵥ fun j => algebraMap F (A F) (z j)) =
      algebraMap F (A F) (qf (1 / 2 : F) B z) := by
  unfold qf
  rw [quad_orth, hO, map_mul]
  congr 1
  exact dot_map (algebraMap F (A F)) B z

lemma integral_of_ne_zero {B : Matrix ι ι F} {ρ : InfinitePlace F → (F →+* ℝ)}
    {P : InfinitePlace F → Matrix ι ι ℝ} {gf : Matrix ι ι (A F)}
    {gi : InfinitePlace F → Matrix ι ι ℝ} (hO : IsOrth B ρ gf gi) {a N : ℕ}
    (hint : ∀ y : ι → A F, (∀ i, (a : A F) * y i ∈ Oh F) → (N : A F) * qf (hf F) (Bf B) y ∈ Oh F)
    (hmem : ∀ b : F, algebraMap F (A F) b ∈ Oh F ↔ ∃ r : 𝓞 F, (r : F) = b)
    {τ : InfinitePlace F → ℂ} {z : ι → F} (h : thTerm B ρ P gf gi (indL a) τ z ≠ 0) :
    ∃ r : 𝓞 F, (r : F) = (N : F) * qf (1 / 2 : F) B z := by
  have hy : ∀ i, (a : A F) * (gf *ᵥ fun j => algebraMap F (A F) (z j)) i ∈ Oh F := by
    by_contra hy
    apply h
    unfold thTerm indL
    rw [Set.indicator_of_notMem (by simpa using hy), zero_mul]
  have := hint _ hy
  rw [qf_adelic hO.1] at this
  rw [← hmem, map_mul, map_natCast]
  exact this

lemma sb_indL (hT2 : T2Space (A F)) (hOc : IsCompact (Oh F)) (hOo : IsOpen (Oh F)) {a : ℕ} (ha : 0 < a) :
    SB (indL a : (ι → A F) → ℂ) := by
  have hcm : Continuous fun y : A F => (a : A F) * y := continuous_const.mul continuous_id
  set L : Set (A F) := {y | (a : A F) * y ∈ Oh F} with hL
  have hLo : IsOpen L := hOo.preimage hcm
  have hLc : IsClosed L := hOc.isClosed.preimage hcm
  have hLk : IsCompact L := by
    have hk : IsCompact ((fun y : A F => algebraMap F (A F) ((a : F)⁻¹) * y) '' Oh F) :=
      hOc.image (continuous_const.mul continuous_id)
    refine hk.of_isClosed_subset hLc ?_
    intro y hy
    refine ⟨_, hy, ?_⟩
    have ha' : (a : F) ≠ 0 := by exact_mod_cast ha.ne'
    have : algebraMap F (A F) ((a : F)⁻¹) * (a : A F) = 1 := by
      rw [← map_natCast (algebraMap F (A F)) a, ← map_mul, inv_mul_cancel₀ ha', map_one]
    simp only [← mul_assoc, this, one_mul]
  have hS : {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F} = Set.pi Set.univ fun _ => L := by
    ext x
    simp [hL]
  have hSo : IsOpen {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F} := by
    rw [hS]
    exact isOpen_set_pi Set.finite_univ fun _ _ => hLo
  have hSc : IsClosed {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F} := by
    rw [hS]
    exact isClosed_set_pi fun _ _ => hLc
  have hSk : IsCompact {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F} := by
    rw [hS]
    exact isCompact_univ_pi fun _ => hLk
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, ?_⟩
  · by_cases hx : x ∈ {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}
    · filter_upwards [hSo.mem_nhds hx] with y hy
      have hy' : y ∈ {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F} := hy
      simp only [indL, Set.indicator_of_mem hx, Set.indicator_of_mem hy']
    · filter_upwards [hSc.isOpen_compl.mem_nhds hx] with y hy
      have hy' : y ∉ {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F} := hy
      simp only [indL, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy']
  exact HasCompactSupport.intro hSk fun x hx => Set.indicator_of_notMem hx _

lemma countable_field : Countable F := by
  have e := (Module.finBasis ℚ F).equivFun
  exact e.toEquiv.countable_iff.mpr inferInstance

end Concrete

theorem fourier_coefficient : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ a : ℕ, 0 < a → ∀ β : F, β ≠ 0 → ∀ N : ℕ, 0 < N → (∃ r : 𝓞 F, (r : F) = (N : F) * β) → (∀ y : ι → A F, (∀ i, (a : A F) * y i ∈ Oh F) → (N : A F) * qf (hf F) (Bf B) y ∈ Oh F) → ∀ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume → ∃ I : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // qf (1 / 2 : F) B x = β}, ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr = (I : ℝ≥0∞) ∧ IntegrableOn (fun x : InfinitePlace F → ℝ => (∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))) D volume ∧ ∫ x in D, (∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = ((volume D).toReal : ℂ) * ((I : ℝ) : ℂ) := by
  intro F _ _ _ _ ι _ _ M B ρ P hQ Ω _ Pr gf gi hC a ha β hβ N hN hNβ hint D hD
  haveI : Countable F := countable_field
  obtain ⟨hTR, -, -, -, hρ, -, -⟩ := id hQ
  obtain ⟨hprob, -, -, hOrth, -⟩ := id hC
  obtain ⟨-, -, hT2, hOc, hOo, -, hmem, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨-, -, -, hfd⟩ := GlobalTheory.T.lattice_fundamental_domain_volume F hTR ρ hρ N hN
  obtain ⟨hvol, horth⟩ := hfd D hD
  have hsb : SB (indL a : (ι → A F) → ℂ) := sb_indL hT2 hOc hOo ha
  obtain ⟨C, hCb⟩ := GlobalTheory.T.weighted_theta_average_le_of_countData F ι M B ρ P hQ Ω Pr gf gi hC (indL a) hsb 1 1 one_pos one_pos
  obtain ⟨hmeas, hbound⟩ := hCb (fun _ => Complex.I) (by simp) (by simp)
  set s : (ι → F) → Ω → ℂ :=
    fun z ω => thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) z with hs
  have hm : ∀ z, Measurable (s z) := hmeas
  have hwt : wt M (fun _ : InfinitePlace F => Complex.I) = 1 := by simp [wt]
  have hnz : ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖s x.1 ω‖ₑ ∂Pr ≠ ∞ := by
    rw [hwt, ENNReal.ofReal_one, one_mul] at hbound
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hfin : ∫⁻ ω, ∑' z, ‖s z ω‖ₑ ∂Pr ≠ ∞ := by
    have hle : ∀ ω, ∑' z, ‖s z ω‖ₑ ≤ 1 + ∑' x : {x : ι → F // x ≠ 0}, ‖s x.1 ω‖ₑ := by
      intro ω
      rw [ENNReal.tsum_eq_add_tsum_ite 0]
      refine add_le_add (thTerm_zero_le B ρ P (gf ω) (gi ω) a) (le_of_eq ?_)
      have := tsum_subtype {x : ι → F | x ≠ 0} (fun z => ‖s z ω‖ₑ)
      refine Eq.trans ?_ this.symm
      refine tsum_congr fun z => ?_
      by_cases h : z = 0 <;> simp [h]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
    rw [lintegral_add_left measurable_const]
    simp only [lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hnz⟩
  have hpos : ∀ z ω, s z ω = ((‖s z ω‖ : ℝ) : ℂ) := fun z ω => thTerm_nonneg B ρ P (gf ω) (gi ω) a z
  set Sel : Set (ι → F) := {z | qf (1 / 2 : F) B z = β} with hSel
  haveI : IsFiniteMeasure ((volume : Measure (InfinitePlace F → ℝ)).restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.ofReal_lt_top⟩
  have hv : Continuous fun x : InfinitePlace F → ℝ =>
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) := by
    simp_rw [ph_neg]
    exact ph_continuous ρ _
  have hvn : ∀ x : InfinitePlace F → ℝ,
      ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))‖ = 1 := by
    intro x
    rw [ph_neg, ph_norm]
  have hres := fourier_series hm hfin (μ := (volume : Measure (InfinitePlace F → ℝ)).restrict D)
    (u := fun z => ph ρ (qf (1 / 2 : F) B z)) (fun z => ph_continuous ρ _) (fun z x => ph_norm ρ _ x)
    hv hvn Sel ((volume D).toReal : ℂ)
    (by
      intro z hz
      have hz' : qf (1 / 2 : F) B z = β := hz
      have : ∀ x : InfinitePlace F → ℝ, ph ρ (qf (1 / 2 : F) B z) x *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = 1 := by
        intro x
        rw [ph_neg, ph_mul, hz', add_neg_cancel, ph_zero]
      simp_rw [this]
      simp [setIntegral_const, Measure.real])
    (by
      intro z hz
      by_cases hall : ∀ ω, s z ω = 0
      · exact Or.inr hall
      left
      push_neg at hall
      obtain ⟨ω, hω⟩ := hall
      obtain ⟨r, hr⟩ := integral_of_ne_zero (hOrth ω) hint hmem hω
      obtain ⟨r₀, hr₀⟩ := hNβ
      have hne : qf (1 / 2 : F) B z + -β ≠ 0 := fun h => hz (add_neg_eq_zero.mp h)
      have := horth _ hne ⟨r - r₀, by
        have hsub : ((r - r₀ : 𝓞 F) : F) = (r : F) - (r₀ : F) := map_sub (algebraMap (𝓞 F) F) r r₀
        rw [hsub, hr, hr₀]
        ring⟩
      have hx : ∀ x : InfinitePlace F → ℝ, ph ρ (qf (1 / 2 : F) B z) x *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) =
          ph ρ (qf (1 / 2 : F) B z + -β) x := by
        intro x
        rw [ph_neg, ph_mul]
      simp_rw [hx]
      exact this)
  have hth : ∀ (x : InfinitePlace F → ℝ) (ω : Ω),
      theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) =
        ∑' z, ph ρ (qf (1 / 2 : F) B z) x * s z ω := fun x ω =>
    tsum_congr fun z => thTerm_shift P (hOrth ω) _ x z
  have hI : ∫⁻ ω, ∑' x : {x : ι → F // qf (1 / 2 : F) B x = β}, ‖s x.1 ω‖ₑ ∂Pr ≠ ∞ :=
    ne_top_of_le_ne_top hfin (lintegral_mono fun ω =>
      ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective fun z => ‖s z ω‖ₑ)
  refine ⟨_, (ENNReal.coe_toNNReal hI).symm, ?_, ?_⟩
  · simp_rw [hth]
    exact hres.1
  · simp_rw [hth]
    rw [hres.2, sum_selected hm hfin hpos Sel]
    rfl

end GlobalTheory.CompanionTheory.SW.CoefTheta
