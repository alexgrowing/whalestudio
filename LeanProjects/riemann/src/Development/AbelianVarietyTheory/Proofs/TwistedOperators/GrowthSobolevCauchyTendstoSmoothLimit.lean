import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RWordRTrAdelic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperations

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Grow GlobalTheory.Mem.AutSpace GlobalTheory.Size Filter Topology
open scoped ENNReal

namespace GlobalTheory.GrowthComplete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {V : HSp D} {N : ℕ} {ψ : ℕ → GA D V → ℂ} {f : GA D V → ℂ}

theorem locUnif {ι : Type} {l : Filter ι} {u : ι → GA D V → ℂ}
    (h : Tendsto (fun i => growthSize V N (u i - f)) l (𝓝 0)) : TendstoLocallyUniformly u f l := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  have hc : Continuous (height V) := (height_laws V).2.2.2.2
  refine ⟨height V ⁻¹' Set.Iio (height V x + 1), (hc.isOpen_preimage _ isOpen_Iio).mem_nhds ?_, ?_⟩
  · show height V x < height V x + 1
    linarith
  have h1x : 1 ≤ height V x := (height_laws V).1 x
  have hH : 0 < (height V x + 1) ^ N := pow_pos (by linarith) N
  have hδ : 0 < ε / (2 * (height V x + 1) ^ N) := by positivity
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 h) _ (ENNReal.ofReal_pos.2 hδ)] with i hi y hy
  have hb := (growthSize_le_iff hδ.le).1 hi y
  have h1 : 1 ≤ height V y := (height_laws V).1 y
  have hy' : height V y ^ N ≤ (height V x + 1) ^ N :=
    pow_le_pow_left₀ (by linarith) (le_of_lt (show height V y < height V x + 1 from hy)) N
  rw [dist_comm, dist_eq_norm]
  calc ‖u i y - f y‖ ≤ ε / (2 * (height V x + 1) ^ N) * height V y ^ N := hb
    _ ≤ ε / (2 * (height V x + 1) ^ N) * (height V x + 1) ^ N := mul_le_mul_of_nonneg_left hy' hδ.le
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

theorem exists_lim (h : Tendsto (fun p : ℕ × ℕ => growthSize V N (ψ p.1 - ψ p.2)) atTop (𝓝 0)) :
    ∃ f : GA D V → ℂ, ∀ g, Tendsto (fun n => ψ n g) atTop (𝓝 (f g)) := by
  have hb : ∀ g, ∀ p : ℕ × ℕ, growthSize V N (ψ p.1 - ψ p.2) ≠ ⊤ →
      dist (ψ p.1 g) (ψ p.2 g) ≤ (growthSize V N (ψ p.1 - ψ p.2)).toReal * height V g ^ N := by
    intro g p hp
    rw [dist_eq_norm]
    exact (growthSize_le_iff ENNReal.toReal_nonneg).1 (ENNReal.ofReal_toReal hp).ge g
  refine ⟨fun g => limUnder atTop (fun n => ψ n g), fun g => ?_⟩
  apply CauchySeq.tendsto_limUnder
  rw [cauchySeq_iff_tendsto_dist_atTop_0]
  have ht : Tendsto (fun p : ℕ × ℕ => (growthSize V N (ψ p.1 - ψ p.2)).toReal * height V g ^ N) atTop (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h).mul_const (height V g ^ N)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun p => dist_nonneg) ?_ ht
  filter_upwards [h.eventually (gt_mem_nhds ENNReal.zero_lt_top)] with p hp
  exact hb g p hp.ne

theorem tendsto_size (h : Tendsto (fun p : ℕ × ℕ => growthSize V N (ψ p.1 - ψ p.2)) atTop (𝓝 0))
    (hf : ∀ g, Tendsto (fun n => ψ n g) atTop (𝓝 (f g))) :
    Tendsto (fun n => growthSize V N (ψ n - f)) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 h) δ hδ)
  filter_upwards [Filter.eventually_ge_atTop (max a.1 a.2)] with n hn
  refine le_trans ?_ hδε.le
  have key : ∀ g, ‖ψ n g - f g‖ ≤ (δ : ℝ) * height V g ^ N := by
    intro g
    refine le_of_tendsto ((hf g).const_sub (ψ n g)).norm ?_
    filter_upwards [Filter.eventually_ge_atTop (max a.1 a.2)] with m hm
    have hnm : growthSize V N (ψ n - ψ m) ≤ ENNReal.ofReal (δ : ℝ) := by
      rw [ENNReal.ofReal_coe_nnreal]
      exact ha (n, m) ⟨le_trans (le_max_left _ _) hn, le_trans (le_max_right _ _) hm⟩
    exact (growthSize_le_iff δ.coe_nonneg).1 hnm g
  have hfin : growthSize V N (ψ n - f) ≤ ENNReal.ofReal (δ : ℝ) := (growthSize_le_iff δ.coe_nonneg).2 key
  rwa [ENNReal.ofReal_coe_nnreal] at hfin

variable (θ N) in

def IsCauchy (ψ : ℕ → GA D V → ℂ) : Prop :=
  (∀ n, Continuous (ψ n) ∧ ψ n ∈ SmFun θ V ∧ ∀ d, growthSob θ V d N (ψ n) ≠ ⊤) ∧
    ∀ d, Tendsto (fun p : ℕ × ℕ => growthSob θ V d N (ψ p.1 - ψ p.2)) atTop (𝓝 0)

theorem map_sub' {T : (GA D V → ℂ) → GA D V → ℂ} (hT : LinOnSm θ V T) {φ φ' : GA D V → ℂ} (h : φ ∈ SmFun θ V)
    (h' : φ' ∈ SmFun θ V) : T (φ - φ') = T φ - T φ' := by
  have h2 : (-1 : ℂ) • φ' ∈ SmFun θ V := (SmFun θ V).smul_mem _ h'
  have e : φ - φ' = φ + (-1 : ℂ) • φ' := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e, hT.add _ h _ h2, hT.smul, neg_one_smul, sub_eq_add_neg]

theorem IsCauchy.size (h : IsCauchy θ N ψ) :
    Tendsto (fun p : ℕ × ℕ => growthSize V N (ψ p.1 - ψ p.2)) atTop (𝓝 0) := by
  obtain ⟨-, hB⟩ := id h
  have h0 := hB 0
  simp only [growthSob, wordSum_zero] at h0
  exact h0

theorem IsCauchy.exists_lim (h : IsCauchy θ N ψ) :
    ∃ f : GA D V → ℂ, ∀ g, Tendsto (fun n => ψ n g) atTop (𝓝 (f g)) := GlobalTheory.GrowthComplete.exists_lim h.size

theorem IsCauchy.tendsto_size (h : IsCauchy θ N ψ) (hf : ∀ g, Tendsto (fun n => ψ n g) atTop (𝓝 (f g))) :
    Tendsto (fun n => growthSize V N (ψ n - f)) atTop (𝓝 0) := GlobalTheory.GrowthComplete.tendsto_size h.size hf

theorem IsCauchy.locUnif (h : IsCauchy θ N ψ) (hf : ∀ g, Tendsto (fun n => ψ n g) atTop (𝓝 (f g))) :
    TendstoLocallyUniformly ψ f atTop := GlobalTheory.GrowthComplete.locUnif (h.tendsto_size hf)

theorem IsCauchy.map (h : IsCauchy θ N ψ) {T : (GA D V → ℂ) → GA D V → ℂ} (hT : LinOnSm θ V T)
    (hc : ∀ n, Continuous (T (ψ n)))
    (hb : ∀ d, ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ φ ∈ SmFun θ V, growthSob θ V d N (T φ) ≤ c * growthSob θ V (d + 1) N φ) :
    IsCauchy θ N fun n => T (ψ n) := by
  obtain ⟨hA, hB⟩ := id h
  unfold IsCauchy
  refine ⟨fun n => ⟨hc n, hT.mem _ (hA n).2.1, fun d => ?_⟩, fun d => ?_⟩
  · obtain ⟨c, hc', hb'⟩ := hb d
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hc' ((hA n).2.2 (d + 1))) (hb' _ (hA n).2.1)
  · obtain ⟨c, hc', hb'⟩ := hb d
    have hlim : Tendsto (fun p : ℕ × ℕ => c * growthSob θ V (d + 1) N (ψ p.1 - ψ p.2)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (hB (d + 1)) (Or.inr hc')
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => by simp) fun p => ?_
    show growthSob θ V d N (T (ψ p.1) - T (ψ p.2)) ≤ c * growthSob θ V (d + 1) N (ψ p.1 - ψ p.2)
    rw [← GlobalTheory.GrowthComplete.map_sub' hT (hA p.1).2.1 (hA p.2).2.1]
    exact hb' _ (sub_mem (hA p.1).2.1 (hA p.2).2.1)

section Der

variable {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem isLieWord_single (hX : X ∈ lieAt V τ) : IsLieWord V [(τ, X)] := by
  simp [IsLieWord, hX]

private theorem exists_growthSob_rder_le_mul_growthSob_succ (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (d : ℕ) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ φ ∈ SmFun θ V,
      growthSob θ V d N (Rder θ V τ X φ) ≤ c * growthSob θ V (d + 1) N φ := by
  obtain ⟨c, hc⟩ := exists_growthSize_rWord_le hθ [(τ, X)] (isLieWord_single hX)
  refine ⟨∑ k ∈ Finset.range (d + 1), ∑ _a : Fin k → D.what₂.Tau × Fin V.rank × Fin V.rank, (c : ℝ≥0∞),
    ?_, fun φ hφ => ?_⟩
  · exact ENNReal.sum_ne_top.2 fun k _ => ENNReal.sum_ne_top.2 fun _ _ => ENNReal.coe_ne_top
  calc growthSob θ V d N (Rder θ V τ X φ)
      = ∑ k ∈ Finset.range (d + 1), ∑ a : Fin k → D.what₂.Tau × Fin V.rank × Fin V.rank,
          growthSize V N (wordAct (glDer θ V) (List.ofFn a) (Rder θ V τ X φ)) := rfl
    _ ≤ ∑ k ∈ Finset.range (d + 1), ∑ _a : Fin k → D.what₂.Tau × Fin V.rank × Fin V.rank,
          (c : ℝ≥0∞) * growthSob θ V (d + 1) N φ := by
        refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun a _ => ?_
        refine hc φ hφ N (d + 1) (List.ofFn a) ?_
        simp only [List.length_ofFn, List.length_cons, List.length_nil, Finset.mem_range] at hk ⊢
        omega
    _ = _ := by simp_rw [Finset.sum_mul]

theorem IsCauchy.rder (hθ : IsInfFam θ) (h : IsCauchy θ N ψ) (hX : X ∈ lieAt V τ) :
    IsCauchy θ N fun n => Rder θ V τ X (ψ n) := by
  obtain ⟨hA, -⟩ := id h
  have hl : IsLieWord V [(τ, X), (τ, X)] := by simp [IsLieWord, hX]
  obtain ⟨c, hc⟩ := exists_growthSize_rWord_le hθ _ hl
  refine h.map (GlobalTheory.Mem.AutSpace.linOnSm_Rder hX) (fun n => ?_) (fun d => exists_growthSob_rder_le_mul_growthSob_succ hθ hX d)
  refine continuous_Rder_of_growth hθ (hA n).2.1 (hA n).1 hX (A := N) (modGrowthExp_iff.2 ?_)
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ((hA n).2.2 2))
    (hc _ (hA n).2.1 N 2 [] (by simp))

theorem IsCauchy.hasDerivAt (hθ : IsInfFam θ) (h : IsCauchy θ N ψ) (hX : X ∈ lieAt V τ)
    (hf : ∀ g, Tendsto (fun n => ψ n g) atTop (𝓝 (f g))) {f' : GA D V → ℂ}
    (hf' : ∀ g, Tendsto (fun n => Rder θ V τ X (ψ n) g) atTop (𝓝 (f' g))) (g : GA D V) :
    HasDerivAt (fun t : ℝ => f (g * oneP θ V τ X t)) (f' g) 0 := by
  have hu : TendstoLocallyUniformly (fun n => Rder θ V τ X (ψ n)) f' atTop := (h.rder hθ hX).locUnif hf'
  have hc : Continuous fun t : ℝ => g * oneP θ V τ X t :=
    continuous_const.mul (GlobalTheory.Mem.Lift.continuous_oneP hθ hX)
  have hd : ∀ n (t : ℝ), HasDerivAt (fun s : ℝ => ψ n (g * oneP θ V τ X s))
      (Rder θ V τ X (ψ n) (g * oneP θ V τ X t)) t := by
    obtain ⟨hA, -⟩ := id h
    intro n t
    exact GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun g' => GlobalTheory.Mem.Lift.hasDerivAt_Rder (hA n).2.1 hX g') g t
  have key := hasDerivAt_of_tendstoLocallyUniformlyOn (l := atTop) (s := Set.univ) (x := (0 : ℝ))
    (f := fun n (s : ℝ) => ψ n (g * oneP θ V τ X s)) (g := fun s : ℝ => f (g * oneP θ V τ X s))
    (f' := fun n (t : ℝ) => Rder θ V τ X (ψ n) (g * oneP θ V τ X t)) (g' := fun t : ℝ => f' (g * oneP θ V τ X t))
    isOpen_univ (tendstoLocallyUniformlyOn_univ.2 (hu.comp _ hc)) (Eventually.of_forall fun n t _ => hd n t)
    (fun t _ => hf _) (Set.mem_univ _)
  simpa [GlobalTheory.Mem.Lift.oneP_zero hθ] using key

theorem IsCauchy.tendsto_rder (hθ : IsInfFam θ) (h : IsCauchy θ N ψ) (hX : X ∈ lieAt V τ)
    (hf : ∀ g, Tendsto (fun n => ψ n g) atTop (𝓝 (f g))) (g : GA D V) :
    Tendsto (fun n => Rder θ V τ X (ψ n) g) atTop (𝓝 (Rder θ V τ X f g)) := by
  obtain ⟨f', hf'⟩ := (h.rder hθ hX).exists_lim
  have hd := h.hasDerivAt hθ hX hf hf' g
  have e : Rder θ V τ X f g = f' g := hd.deriv
  rw [e]
  exact hf' g

end Der

theorem IsCauchy.continuous (h : IsCauchy θ N ψ) (hf : ∀ g, Tendsto (fun n => ψ n g) atTop (𝓝 (f g))) :
    Continuous f := by
  obtain ⟨hA, -⟩ := id h
  exact (h.locUnif hf).continuous (Eventually.of_forall fun n => (hA n).1).frequently

theorem IsCauchy.smooth (hθ : IsInfFam θ) (h : IsCauchy θ N ψ) (hf : ∀ g, Tendsto (fun n => ψ n g) atTop (𝓝 (f g))) :
    f ∈ SmFun θ V := by
  have hcont : ∀ φ ∈ {φ : GA D V → ℂ | ∃ χ : ℕ → GA D V → ℂ, IsCauchy θ N χ ∧
      ∀ g, Tendsto (fun n => χ n g) atTop (𝓝 (φ g))}, Continuous φ := by
    rintro φ ⟨χ, hχ, hl⟩
    exact hχ.continuous hl
  have hder : ∀ φ ∈ {φ : GA D V → ℂ | ∃ χ : ℕ → GA D V → ℂ, IsCauchy θ N χ ∧
      ∀ g, Tendsto (fun n => χ n g) atTop (𝓝 (φ g))}, ∀ τ', ∀ X' ∈ lieAt V τ',
      ∃ φ' ∈ {φ : GA D V → ℂ | ∃ χ : ℕ → GA D V → ℂ, IsCauchy θ N χ ∧
        ∀ g, Tendsto (fun n => χ n g) atTop (𝓝 (φ g))},
        ∀ g, HasDerivAt (fun t : ℝ => φ (g * oneP θ V τ' X' t)) (φ' g) 0 := by
    rintro φ ⟨χ, hχ, hl⟩ τ' X' hX'
    obtain ⟨φ', hφ'⟩ := (hχ.rder hθ hX').exists_lim
    exact ⟨φ', ⟨_, hχ.rder hθ hX', hφ'⟩, hχ.hasDerivAt hθ hX' hl hφ'⟩
  exact GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ V _ hcont hder f ⟨ψ, h, hf⟩

theorem IsCauchy.letter (hθ : IsInfFam θ) (h : IsCauchy θ N ψ) (hf : ∀ g, Tendsto (fun n => ψ n g) atTop (𝓝 (f g)))
    (a : D.what₂.Tau × Fin V.rank × Fin V.rank) : (IsCauchy θ N fun n => glDer θ V a (ψ n)) ∧
      ∀ g, Tendsto (fun n => glDer θ V a (ψ n) g) atTop (𝓝 (glDer θ V a f g)) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V a.1 (Matrix.single a.2.1 a.2.2 1)
  have e : ∀ φ : GA D V → ℂ, glDer θ V a φ =
      Rder θ V a.1 ((1 / 2 : ℂ) • (Matrix.single a.2.1 a.2.2 1 + conjAt V a.1 (Matrix.single a.2.1 a.2.2 1))) φ +
        Complex.I • Rder θ V a.1 ((1 / (2 * Complex.I)) •
          (Matrix.single a.2.1 a.2.2 1 - conjAt V a.1 (Matrix.single a.2.1 a.2.2 1))) φ := fun φ => rfl
  obtain ⟨hA1, -⟩ := id (h.rder hθ h1)
  obtain ⟨hA2, -⟩ := id (h.rder hθ h2)
  have hT : LinOnSm θ V (glDer θ V a) := GlobalTheory.Mem.AutSpace.linOnSm_RderC a.1 (Matrix.single a.2.1 a.2.2 1)
  refine ⟨h.map hT (fun n => ?_) (fun d => ⟨1, ENNReal.one_ne_top, fun φ _ => ?_⟩), fun g => ?_⟩
  · rw [e]
    exact (hA1 n).1.add (continuous_const.smul (hA2 n).1)
  · rw [one_mul]
    exact wordSum_letter_le (A := glDer θ V) (p := growthSize V N) d a φ
  · simp only [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (h.tendsto_rder hθ h1 hf g).add ((h.tendsto_rder hθ h2 hf g).const_mul _)

theorem IsCauchy.word (hθ : IsInfFam θ) (h : IsCauchy θ N ψ) (hf : ∀ g, Tendsto (fun n => ψ n g) atTop (𝓝 (f g)))
    (l : List (D.what₂.Tau × Fin V.rank × Fin V.rank)) : (IsCauchy θ N fun n => wordAct (glDer θ V) l (ψ n)) ∧
      ∀ g, Tendsto (fun n => wordAct (glDer θ V) l (ψ n) g) atTop (𝓝 (wordAct (glDer θ V) l f g)) := by
  induction l with
  | nil =>
    simp only [wordAct_nil]
    exact ⟨h, hf⟩
  | cons a l ih =>
    simp only [wordAct_cons]
    exact ih.1.letter hθ ih.2 a

theorem complete : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (N : ℕ) (ψ : ℕ → GA D V → ℂ), (∀ n, Continuous (ψ n) ∧ ψ n ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (ψ n) ≠ ⊤) → (∀ d, Filter.Tendsto (fun p : ℕ × ℕ => GlobalTheory.Size.growthSob θ V d N (ψ p.1 - ψ p.2)) Filter.atTop (nhds 0)) → ∃ f : GA D V → ℂ, Continuous f ∧ f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, Filter.Tendsto (fun n => GlobalTheory.Size.growthSob θ V d N (ψ n - f)) Filter.atTop (nhds 0) := by
  intro D θ hθ V N ψ h1 h2
  have h : IsCauchy θ N ψ := by
    unfold IsCauchy
    exact ⟨h1, h2⟩
  obtain ⟨f, hf⟩ := h.exists_lim
  have hs : f ∈ SmFun θ V := h.smooth hθ hf
  refine ⟨f, h.continuous hf, hs, fun d => ?_⟩
  have key : ∀ l : List (D.what₂.Tau × Fin V.rank × Fin V.rank),
      Tendsto (fun n => growthSize V N (wordAct (glDer θ V) l (ψ n - f))) atTop (𝓝 0) := by
    intro l
    obtain ⟨hl1, hl2⟩ := h.word hθ hf l
    refine (hl1.tendsto_size hl2).congr fun n => ?_
    rw [GlobalTheory.GrowthComplete.map_sub' (linOnSm_glWord (θ := θ) l) (h1 n).2.1 hs]
  have hsum := tendsto_finsetSum (Finset.range (d + 1)) fun k _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin k → D.what₂.Tau × Fin V.rank × Fin V.rank)) fun a _ =>
      key (List.ofFn a)
  simp only [Finset.sum_const_zero] at hsum
  exact hsum

end GlobalTheory.GrowthComplete

end
