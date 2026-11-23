import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal

namespace UpperTheory.Esk.HyperbolicTermsContribution

open UpperTheory.Esk

theorem vecMul_ne {F : Type} [Field F] (s : Fin 2 → F) (hs : s ≠ 0) (δ : GL (Fin 2) F) : s ᵥ* δ.val ≠ 0 := by
  intro h
  apply hs
  have h2 := congrArg (fun v => v ᵥ* (δ⁻¹ : GL (Fin 2) F).val) h
  simpa [Matrix.vecMul_vecMul] using h2

theorem isEll_conj {F : Type} [Field F]
    (hfix : ∀ (s : Fin 2 → F) (γ δ : GL (Fin 2) F), Fix s ((δ : PG F) * γ * (δ : PG F)⁻¹) ↔
      ∃ c : F, (s ᵥ* δ.val) ᵥ* γ.val = c • (s ᵥ* δ.val)) (g γ : PG F) :
    IsEll (g * γ * g⁻¹) ↔ IsEll γ := by
  obtain ⟨δ, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective γ
  have h1 : ∀ s : Fin 2 → F, Fix s (γ : PG F) ↔ ∃ c : F, s ᵥ* γ.val = c • s := by
    intro s
    have := hfix s γ 1
    simpa using this
  constructor
  · intro h s hs hf
    obtain ⟨c, hc⟩ := (h1 s).1 hf
    have hs' : s ᵥ* (δ⁻¹ : GL (Fin 2) F).val ≠ 0 := vecMul_ne s hs _
    apply h _ hs'
    rw [hfix]
    refine ⟨c, ?_⟩
    have e : (s ᵥ* (δ⁻¹ : GL (Fin 2) F).val) ᵥ* δ.val = s := by
      rw [Matrix.vecMul_vecMul]; simp
    rw [e, hc]
  · intro h s hs hf
    obtain ⟨c, hc⟩ := (hfix s γ δ).1 hf
    exact h _ (vecMul_ne s hs δ) ((h1 _).2 ⟨c, hc⟩)

variable {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι]

open Classical in

def uT (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (T : ℝ) (γ : PG F) (y : D.Y) : ℂ :=
  if IsEll γ then 0 else (D.LamF T γ).indicator (D.kk k a γ) y

theorem enorm_uT_le (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (T : ℝ) (γ : PG F) (y : D.Y) :
    ‖uT D k a T γ y‖ₑ ≤ ‖(D.LamF T γ).indicator (D.kk k a γ) y‖ₑ := by
  unfold uT
  split_ifs <;> simp

theorem enorm_ind_le (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (T : ℝ) (γ : PG F) (y : D.Y) :
    ‖(D.LamF T γ).indicator (D.kk k a γ) y‖ₑ ≤ ‖D.kk k a γ y‖ₑ := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> simp

open Classical in
theorem fhyp (hC4 : C4) (hE0a : E0a) (hE0c : KernelTermsInvariantBounded) (hE0d : E0d) (hE2 : E2) (hE3 : E3) (hEcut : Ecut)
    (hFsum : Fsum) (hF5 : F5) (hF6 : F6) (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (hyp : D.Hyp k a)
    (b : D.Y → ℝ) (hb : IsCut (PG F) b)
    (hint : Integrable (fun y => b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) D.μY) :
    ∫ y, b y • (∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) ∂D.μY = 0 := by
  have hax := hyp.ax
  obtain ⟨hcnt, hsf, hpres, -, -, -, -, -⟩ := hE0a F I Gf D hax
  obtain ⟨-, hkkc, hkkm, -, -, -⟩ := hE0c F I Gf ι D k a hyp
  obtain ⟨-, -, -, -, -, -, -, hLamF, hev, -, hfix⟩ := hE0d F I Gf D hax
  obtain ⟨-, hE2'⟩ := hE2 F I Gf ι D k a hyp
  have hb3 := hE3 F I Gf D hax b hb
  obtain ⟨-, hcut⟩ := hEcut F I Gf D hax
  obtain ⟨C, hC⟩ := hF5 F I Gf ι D k a hyp
  have hF6' := hF6 F I Gf ι D k a hyp
  have : Countable (PG F) := hcnt
  have : Countable D.Cj := hcnt
  have : Countable D.Om := hax.cO

  have hbI : Integrable b D.μY := by
    refine ⟨hb.meas.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (le_of_eq ?_) hb3
    refine lintegral_congr fun y => ?_
    exact Real.enorm_eq_ofReal (hb.nonneg y)

  have hum : ∀ T γ, Measurable (uT D k a T γ) := by
    intro T γ
    by_cases h : IsEll γ
    · unfold uT; simp only [h, if_true]; exact measurable_const
    · unfold uT; simp only [h, if_false]; exact (hkkm γ).indicator (hLamF T γ).1

  have hsumle : ∀ T : ℝ, 1 < T → ∀ y, y ∉ D.abelian₂ T → ∑' γ, ‖uT D k a T γ y‖ₑ ≤ C := by
    intro T hT y hy
    exact le_trans (ENNReal.tsum_le_tsum fun γ => enorm_uT_le D k a T γ y) ((hC T hT y).2 hy)
  have hon : ∀ T : ℝ, 1 < T → ∀ y, y ∈ D.abelian₂ T → ∀ γ, uT D k a T γ y = if IsEll γ then 0 else D.kk k a γ y := by
    intro T hT y hy γ
    unfold uT
    split_ifs
    · rfl
    · exact Set.indicator_of_mem ((hC T hT y).1 hy γ) _

  have hinv : ∀ T (g γ : PG F) (y : D.Y), uT D k a T (g * γ * g⁻¹) (g • y) = uT D k a T γ y := by
    intro T g γ y
    unfold uT
    rw [isEll_conj hfix g γ]
    split_ifs
    · rfl
    · rw [Set.indicator_apply, Set.indicator_apply, hkkc]
      simp only [(hLamF T γ).2 g y]

  have step1 : ∀ T : ℝ, 1 < T → Integrable (fun y => b y • ∑' γ, uT D k a T γ y) D.μY ∧
      ∫ y, b y • ∑' γ, uT D k a T γ y ∂D.μY = 0 := by
    intro T hT
    obtain ⟨CT, hCT⟩ := hE2' T
    have hfin : ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖uT D k a T γ y‖ₑ ∂D.μY < ⊤ := by
      have hle : ∀ y, ∑' γ, ‖uT D k a T γ y‖ₑ ≤ (CT : ℝ≥0∞) + C := by
        intro y
        by_cases hy : y ∈ D.abelian₂ T
        · refine le_trans ?_ le_self_add
          refine le_trans (ENNReal.tsum_le_tsum fun γ => ?_) (hCT y hy)
          exact (enorm_uT_le D k a T γ y).trans (enorm_ind_le D k a T γ y)
        · exact (hsumle T hT y hy).trans le_add_self
      calc ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖uT D k a T γ y‖ₑ ∂D.μY
          ≤ ∫⁻ y, ENNReal.ofReal (b y) * ((CT : ℝ≥0∞) + C) ∂D.μY :=
            lintegral_mono fun y => by gcongr; exact hle y
        _ = (∫⁻ y, ENNReal.ofReal (b y) ∂D.μY) * ((CT : ℝ≥0∞) + C) :=
            lintegral_mul_const' _ _ (by simp)
        _ < ⊤ := ENNReal.mul_lt_top hb3 (by simp)
    obtain ⟨hb', hFs⟩ := hFsum F I Gf D hax b hb
    obtain ⟨hm', hi', hiY, heq⟩ := hFs (uT D k a T) (hum T) hfin
    refine ⟨hiY, ?_⟩
    rw [heq]

    let R : Set (D.Cj × D.Om) := Set.range (fun q : MulAction.orbitRel.Quotient (PG F) (D.Cj × D.Om) => q.out)
    have hR : ∀ ω : D.Cj × D.Om, ∃! r, r ∈ R ∧ r ∈ MulAction.orbit (PG F) ω := by
      intro ω
      refine ⟨(Quotient.mk (MulAction.orbitRel (PG F) (D.Cj × D.Om)) ω).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
      · exact (MulAction.orbitRel_apply).1 (Quotient.mk_out ω)
      · rintro r ⟨⟨q, rfl⟩, hq⟩
        have e1 : q = Quotient.mk (MulAction.orbitRel (PG F) (D.Cj × D.Om)) ω := by
          rw [← Quotient.out_eq q]
          exact Quotient.sound ((MulAction.orbitRel_apply).2 hq)
        rw [e1]
    have hβ : ∀ r : D.Cj × D.Om, ∃ β : D.Xs → ℝ, IsCut (MulAction.stabilizer (PG F) r) β := by
      intro r
      refine hcut r.2 _ ?_
      intro g hg
      rw [MulAction.mem_stabilizer_iff] at hg ⊢
      have := congrArg Prod.snd hg
      simpa using this
    choose β hβ using hβ
    have hinv' : ∀ (g : PG F) (p : (D.Cj × D.Om) × D.Xs),
        uT D k a T (D.el (g • p).1.1) ((g • p).1.2, (g • p).2) = uT D k a T (D.el p.1.1) (p.1.2, p.2) := by
      intro g p
      have e : ((g • p).1.2, (g • p).2) = g • ((p.1.2, p.2) : D.Y) := rfl
      rw [e, show D.el (g • p).1.1 = g * D.el p.1.1 * g⁻¹ from D.smulC g p.1.1, hinv]
    obtain ⟨hI, hS⟩ := hC4 (PG F) (D.Cj × D.Om) D.Xs volume hpres _ hb' _ hm' hinv' hi' R hR β (fun r _ => hβ r)
    have hz : ∀ r : R, ∫ x, β r x • uT D k a T (D.el r.1.1) (r.1.2, x) = 0 := by
      intro r
      by_cases he : IsEll (D.el r.1.1)
      · simp [uT, he]
      · have hI' := hI r.1 r.2
        simp only [uT, he, if_false] at hI' ⊢
        exact hF6' T hT (D.el r.1.1) r.1.2 he (β r.1) (hβ r.1) hI'
    have hS' := hS
    simp only [hz] at hS'
    exact (hS'.unique hasSum_zero)

  have hT2 : ∀ n : ℕ, (1 : ℝ) < (n : ℝ) + 2 := fun n => by
    have := n.cast_nonneg (α := ℝ)
    linarith
  have hlim : Tendsto (fun n : ℕ => ∫ y, b y • ∑' γ, uT D k a ((n : ℝ) + 2) γ y ∂D.μY) atTop
      (𝓝 (∫ y, b y • (∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) ∂D.μY)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => ‖b y • ∑' γ : PG F, (if IsEll γ then 0 else D.kk k a γ y)‖ + b y * C)
      (fun n => (step1 _ (hT2 n)).1.aestronglyMeasurable) (hint.norm.add (hbI.mul_const _)) ?_ ?_
    · intro n
      refine Filter.Eventually.of_forall fun y => ?_
      have hT : (1 : ℝ) < (n : ℝ) + 2 := hT2 n
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (hb.nonneg y), ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (hb.nonneg y)
      by_cases hy : y ∈ D.abelian₂ ((n : ℝ) + 2)
      · rw [tsum_congr (hon _ hT y hy)]
        exact le_add_of_nonneg_right C.2
      · have h1 : ‖∑' γ, uT D k a ((n : ℝ) + 2) γ y‖ₑ ≤ C :=
          enorm_tsum_le_tsum_enorm.trans (hsumle _ hT y hy)
        have h2 : ‖∑' γ, uT D k a ((n : ℝ) + 2) γ y‖ ≤ C := by
          have := ENNReal.toReal_mono ENNReal.coe_ne_top h1
          simpa using this
        exact h2.trans (le_add_of_nonneg_left (norm_nonneg _))
    · refine Filter.Eventually.of_forall fun y => ?_
      obtain ⟨T₀, hT₀⟩ := hev y
      obtain ⟨N, hN⟩ := exists_nat_ge T₀
      refine tendsto_const_nhds.congr' ?_
      refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      have hT : (1 : ℝ) < (n : ℝ) + 2 := hT2 n
      have hy : y ∈ D.abelian₂ ((n : ℝ) + 2) := hT₀ _ (by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
      dsimp only
      rw [tsum_congr (hon _ hT y hy)]
  have h0 : Tendsto (fun n : ℕ => ∫ y, b y • ∑' γ, uT D k a ((n : ℝ) + 2) γ y ∂D.μY) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => ?_)
    exact ((step1 _ (hT2 n)).2).symm
  exact tendsto_nhds_unique hlim h0

end UpperTheory.Esk.HyperbolicTermsContribution

theorem UpperTheory.Esk.pf_Fhyp : UpperTheory.Esk.C4 → UpperTheory.Esk.E0a → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.E2 → UpperTheory.Esk.E3 → UpperTheory.Esk.Ecut → UpperTheory.Esk.Fsum → UpperTheory.Esk.F5 → UpperTheory.Esk.F6 → UpperTheory.Esk.Fhyp := by
  intro hC4 hE0a hE0c hE0d hE2 hE3 hEcut hFsum hF5 hF6 F I Gf ι _ _ _ _ D k a hyp b hb hint
  exact UpperTheory.Esk.HyperbolicTermsContribution.fhyp hC4 hE0a hE0c hE0d hE2 hE3 hEcut hFsum hF5 hF6 D k a hyp b hb hint
