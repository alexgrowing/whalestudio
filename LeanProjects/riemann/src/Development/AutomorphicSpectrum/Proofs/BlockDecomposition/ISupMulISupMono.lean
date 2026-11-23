import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductLintegralLimitStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PureAdelicFunctionMeasurableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ISupFiniteProductTailLimit
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureZero

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimFormula

theorem iSup_mul_iSup_mono {a c : ℕ → ℝ≥0∞} (ha : Monotone a) (hc : Monotone c) :
    (⨆ k, a k) * (⨆ k, c k) = ⨆ k, a k * c k := by
  rw [ENNReal.iSup_mul]
  simp_rw [ENNReal.mul_iSup]
  refine le_antisymm (iSup_le fun i => iSup_le fun j => ?_)
    (iSup_le fun k => le_iSup_of_le k (le_iSup_of_le k le_rfl))
  exact le_iSup_of_le (max i j) (mul_le_mul' (ha (le_max_left i j)) (hc (le_max_right i j)))

theorem prod_iSup_mono {ι : Type} (s : Finset ι) (f : ι → ℕ → ℝ≥0∞) (hf : ∀ a, Monotone (f a)) :
    ∏ a ∈ s, ⨆ k, f a k = ⨆ k, ∏ a ∈ s, f a k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [ih, iSup_mul_iSup_mono (hf a)
      (fun k l hkl => Finset.prod_le_prod' fun i _ => hf i hkl)]

theorem exists_approx {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (f : α → ℝ≥0∞)
    (hf : Measurable f) :
    ∃ g : ℕ → α → ℝ≥0∞, (∀ k, Measurable (g k)) ∧ (∀ x, Monotone fun k => g k x) ∧
      (∀ x, ⨆ k, g k x = f x) ∧ ∀ k, ∫⁻ x, g k x ∂μ ≠ ⊤ := by
  refine ⟨fun k => (spanningSets μ k).indicator fun x => min (f x) (k : ℝ≥0∞), fun k => ?_,
    fun x k l hkl => ?_, fun x => ?_, fun k => ?_⟩
  · exact (hf.min measurable_const).indicator (measurableSet_spanningSets μ k)
  · by_cases hx : x ∈ spanningSets μ k
    · have hx' : x ∈ spanningSets μ l := monotone_spanningSets μ hkl hx
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
      exact min_le_min_left _ (by exact_mod_cast hkl)
    · simp only [Set.indicator_of_notMem hx]
      exact zero_le
  · refine le_antisymm (iSup_le fun k => ?_) ?_
    · by_cases hx : x ∈ spanningSets μ k
      · simp only [Set.indicator_of_mem hx]
        exact min_le_left _ _
      · simp only [Set.indicator_of_notMem hx]
        exact zero_le
    · have hx : x ∈ ⋃ k, spanningSets μ k := by
        rw [iUnion_spanningSets]
        trivial
      obtain ⟨k₀, hk₀⟩ := Set.mem_iUnion.1 hx
      have hlim : Tendsto (fun n : ℕ => min (f x) (n : ℝ≥0∞)) atTop (𝓝 (min (f x) ⊤)) :=
        tendsto_const_nhds.min ENNReal.tendsto_nat_nhds_top
      rw [min_eq_left le_top] at hlim
      refine le_of_tendsto hlim (eventually_atTop.2 ⟨k₀, fun n hn => ?_⟩)
      refine le_iSup_of_le n ?_
      simp only [Set.indicator_of_mem (monotone_spanningSets μ hn hk₀)]
      exact le_rfl
  · have hle : ∫⁻ x, (spanningSets μ k).indicator (fun x => min (f x) (k : ℝ≥0∞)) x ∂μ ≤
        ∫⁻ x, (spanningSets μ k).indicator (fun _ => (k : ℝ≥0∞)) x ∂μ :=
      lintegral_mono fun x => Set.indicator_le_indicator (min_le_right _ _)
    rw [lintegral_indicator_const (measurableSet_spanningSets μ k)] at hle
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) (measure_spanningSets_lt_top μ k).ne) hle

theorem partial_tendsto {ι : Type} [DecidableEq ι] (x : ι → ℝ) (S : Finset ι)
    (hx : Summable (fun v => |x v - 1|)) :
    Tendsto (fun S' : Finset ι => ∏ v ∈ (S ∪ S') \ S, x v) atTop
      (𝓝 (∏' v : {v // v ∉ S}, x v.1)) := by
  have hU : Tendsto (fun S' : Finset ι => S ∪ S') atTop atTop :=
    tendsto_atTop_mono (fun S' => Finset.subset_union_right) tendsto_id
  have tails : Tendsto (fun S' : Finset ι => ∏' v : {v // v ∉ S ∪ S'}, x v.1) atTop (𝓝 1) :=
    (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one x hx).comp hU
  have hdiv := (tendsto_const_nhds (x := ∏' v : {v // v ∉ S}, x v.1)).div tails one_ne_zero
  rw [div_one] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [tails.eventually_ne one_ne_zero] with S' hne
  show (∏' v : {v // v ∉ S}, x v.1) / (∏' v : {v // v ∉ S ∪ S'}, x v.1) = _
  rw [GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι x S (S ∪ S') hx Finset.subset_union_left,
    mul_div_assoc, div_self hne, mul_one]

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

open Classical in

def phi (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞)
    (v : HeightOneSpectrum (𝓞 F)) : (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞ :=
  if v ∈ S then Ψ v else (primV σ J b v).indicator fun _ => 1

def cut (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (S T : Finset (HeightOneSpectrum (𝓞 F))) : Set (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) :=
  {y | (∀ v, v ∉ T → projV v (projFin y) ∈ latV b v) ∧
    ∀ v, v ∈ T → v ∉ S → projV v (projFin y) ∈ primV σ J b v}

open Classical in

theorem pureL_phi (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin d) F E) {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T)
    (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞)
    (y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E) :
    pureL b T Ψinf (phi σ J b S Ψ) y =
      (cut σ J b S T).indicator
        (fun Y => Ψinf (projInf Y) * ∏ v ∈ S, Ψ v (projV v (projFin Y))) y := by
  have hprod : ∏ v ∈ T, phi σ J b S Ψ v (projV v (projFin y)) =
      (∏ v ∈ T \ S, (primV σ J b v).indicator (fun _ => (1 : ℝ≥0∞)) (projV v (projFin y))) *
        ∏ v ∈ S, Ψ v (projV v (projFin y)) := by
    rw [← Finset.prod_sdiff hST]
    congr 1
    · exact Finset.prod_congr rfl fun v hv => by simp [phi, (Finset.mem_sdiff.1 hv).2]
    · exact Finset.prod_congr rfl fun v hv => by simp [phi, hv]
  unfold pureL
  by_cases h1 : y ∈ intOff (n := 1) (M := M + 2) b T
  · rw [Set.indicator_of_mem h1]
    show Ψinf (projInf y) * ∏ v ∈ T, phi σ J b S Ψ v (projV v (projFin y)) = _
    rw [hprod]
    by_cases h2 : ∀ v, v ∈ T → v ∉ S → projV v (projFin y) ∈ primV σ J b v
    · have hy : y ∈ cut σ J b S T := ⟨h1, h2⟩
      rw [Set.indicator_of_mem hy, Finset.prod_eq_one, one_mul]
      intro v hv
      exact Set.indicator_of_mem
        (h2 v (Finset.mem_sdiff.1 hv).1 (Finset.mem_sdiff.1 hv).2) _
    · have hy : y ∉ cut σ J b S T := fun h => h2 h.2
      rw [Set.indicator_of_notMem hy]
      push_neg at h2
      obtain ⟨v, hvT, hvS, hv⟩ := h2
      rw [Finset.prod_eq_zero (Finset.mem_sdiff.2 ⟨hvT, hvS⟩) (Set.indicator_of_notMem hv _)]
      simp
  · have hy : y ∉ cut σ J b S T := fun h => h1 h.1
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem hy]

end Places

section Finite

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finite_case (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin d) F E) (I : Measure (Fin 1 → Fin (M + 2) → AF F ⊗[F] E))
    (minf : Measure (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E))
    (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E))
    (hlat : ∀ v, m v (latV b v) < ⊤)
    (hsum : Summable (fun v => |(m v (latV b v)).toReal - 1|))
    {S₀ S₁ S : Finset (HeightOneSpectrum (𝓞 F))}
    (hE : ∀ S, S₀ ⊆ S →
      ∀ (φinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞)
        (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞),
        Measurable φinf → (∀ v, Measurable (φ v)) →
        ∫⁻ X, pureL b S φinf φ X ∂I =
          ((1 : ℝ≥0) : ℝ≥0∞) * ((∫⁻ X, φinf X ∂minf) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v)) *
            ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal))
    (hprim : ∀ v, v ∉ S₁ → primV σ J b v ⊆ latV b v ∧ MeasurableSet (primV σ J b v))
    (hsumP : Summable (fun v => |(m v (primV σ J b v)).toReal - 1|))
    (hS₀ : S₀ ⊆ S) (hS₁ : S₁ ⊆ S)
    (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞)
    (hΨinf : Measurable Ψinf) (hΨ : ∀ v, Measurable (Ψ v))
    (hfi : ∫⁻ y, Ψinf y ∂minf ≠ ⊤) (hfv : ∀ v ∈ S, ∫⁻ y, Ψ v y ∂(m v) ≠ ⊤) :
    ∫⁻ y, purePr σ J b S Ψinf Ψ y ∂I =
      ((∫⁻ y, Ψinf y ∂minf) * ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m v)) *
        ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (primV σ J b v.1)).toReal) := by
  classical
  haveI := GlobalTheory.CompanionTheory.SW.EulerZero.countable_places F
  obtain ⟨u, hu, hut⟩ :=
    exists_seq_monotone_tendsto_atTop_atTop (Finset (HeightOneSpectrum (𝓞 F)))
  let T : ℕ → Finset (HeightOneSpectrum (𝓞 F)) := fun k => S ∪ u k
  have hTm : Monotone T := fun k l h => Finset.union_subset_union_right (hu h)
  have hST : ∀ k, S ⊆ T k := fun k => Finset.subset_union_left
  have hTt : Tendsto T atTop atTop :=
    tendsto_atTop_mono (fun k => (Finset.subset_union_right : u k ⊆ S ∪ u k)) hut
  have hφ : ∀ v, Measurable (phi σ J b S Ψ v) := by
    intro v
    by_cases hv : v ∈ S
    · simpa [phi, hv] using hΨ v
    · have hv1 : v ∉ S₁ := fun h => hv (hS₁ h)
      simpa [phi, hv] using (measurable_const (a := (1 : ℝ≥0∞))).indicator (hprim v hv1).2
  let A : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞ :=
    fun Y => Ψinf (projInf Y) * ∏ v ∈ S, Ψ v (projV v (projFin Y))
  let f : ℕ → (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞ :=
    fun k => pureL b (T k) Ψinf (phi σ J b S Ψ)
  have hfm : ∀ k, Measurable (f k) := fun k =>
    GlobalTheory.T.pure_adelic_function_measurable F E σ hσ d b 1 (M + 2) (T k) Ψinf _ hΨinf hφ
  have hfeq : ∀ k y, f k y = (cut σ J b S (T k)).indicator A y := fun k y =>
    pureL_phi σ J b (hST k) Ψinf Ψ y
  have hcut : ∀ k l, k ≤ l → cut σ J b S (T l) ⊆ cut σ J b S (T k) := by
    intro k l hkl y hy
    refine ⟨fun v hv => ?_, fun v hv hvS => hy.2 v (hTm hkl hv) hvS⟩
    have hvS : v ∉ S := fun h => hv (hST k h)
    by_cases hvl : v ∈ T l
    · exact (hprim v fun h => hvS (hS₁ h)).1 (hy.2 v hvl hvS)
    · exact hy.1 v hvl
  have hanti : Antitone f := by
    intro k l hkl y
    rw [hfeq, hfeq]
    exact Set.indicator_le_indicator_of_subset (hcut k l hkl) (fun _ => zero_le) y
  have hinf : ∀ y, ⨅ k, f k y = purePr σ J b S Ψinf Ψ y := by
    intro y
    unfold purePr
    by_cases hy : ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v
    · have hmem : ∀ k, y ∈ cut σ J b S (T k) := fun k =>
        ⟨fun v hv => (hprim v fun h => hv (hST k (hS₁ h))).1 (hy v fun h => hv (hST k h)),
          fun v _ hvS => hy v hvS⟩
      rw [Set.indicator_of_mem (show y ∈ {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E |
        ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v} from hy)]
      simp only [hfeq, Set.indicator_of_mem (hmem _)]
      exact iInf_const
    · rw [Set.indicator_of_notMem (show y ∉ {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E |
        ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v} from hy)]
      push_neg at hy
      obtain ⟨v, hvS, hv⟩ := hy
      obtain ⟨k, hk⟩ := (hut.eventually_ge_atTop ({v} : Finset _)).exists
      have hvk : v ∈ T k := Finset.mem_union_right _ (hk (Finset.mem_singleton_self v))
      have hyk : y ∉ cut σ J b S (T k) := fun h => hv (h.2 v hvk hvS)
      refine le_antisymm (iInf_le_of_le k ?_) zero_le
      rw [hfeq, Set.indicator_of_notMem hyk]
  let B : ℝ≥0∞ := (∫⁻ y, Ψinf y ∂minf) * ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m v)
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top hfi (ENNReal.prod_ne_top hfv)
  let x : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (m v (primV σ J b v)).toReal
  let l : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (m v (latV b v)).toReal
  have hx0 : ∀ k, 0 ≤ ∏ v ∈ T k \ S, x v := fun k =>
    Finset.prod_nonneg fun v _ => ENNReal.toReal_nonneg
  have hint : ∀ k, ∫⁻ y, f k y ∂I =
      B * ENNReal.ofReal ((∏ v ∈ T k \ S, x v) * ∏' v : {v // v ∉ T k}, l v.1) := by
    intro k
    have hphiS : ∏ v ∈ T k, ∫⁻ y, phi σ J b S Ψ v y ∂(m v) =
        (∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m v)) * ENNReal.ofReal (∏ v ∈ T k \ S, x v) := by
      rw [← Finset.prod_sdiff (hST k), mul_comm]
      congr 1
      · exact Finset.prod_congr rfl fun v hv => by simp [phi, hv]
      · rw [ENNReal.ofReal_prod_of_nonneg fun _ _ => ENNReal.toReal_nonneg]
        refine Finset.prod_congr rfl fun v hv => ?_
        have hvS : v ∉ S := (Finset.mem_sdiff.1 hv).2
        have hv1 : v ∉ S₁ := fun h => hvS (hS₁ h)
        have hfin : m v (primV σ J b v) ≠ ⊤ :=
          ne_top_of_le_ne_top (hlat v).ne (measure_mono (hprim v hv1).1)
        have hphi : phi σ J b S Ψ v = (primV σ J b v).indicator fun _ => 1 := by
          simp [phi, hvS]
        rw [hphi, lintegral_indicator_const (hprim v hv1).2, one_mul]
        exact (ENNReal.ofReal_toReal hfin).symm
    show ∫⁻ y, pureL b (T k) Ψinf (phi σ J b S Ψ) y ∂I = _
    rw [hE (T k) (hS₀.trans (hST k)) Ψinf _ hΨinf hφ, hphiS, ENNReal.ofReal_mul (hx0 k)]
    simp only [ENNReal.coe_one, one_mul, B, mul_assoc]
    rfl
  have hp : Tendsto (fun k => ∏ v ∈ T k \ S, x v) atTop (𝓝 (∏' v : {v // v ∉ S}, x v.1)) :=
    (partial_tendsto x S hsumP).comp hut
  have hq : Tendsto (fun k => ∏' v : {v // v ∉ T k}, l v.1) atTop (𝓝 1) :=
    (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one l hsum).comp hTt
  have hpq := hp.mul hq
  rw [mul_one] at hpq
  have hlim : Tendsto (fun k => ∫⁻ y, f k y ∂I) atTop
      (𝓝 (B * ENNReal.ofReal (∏' v : {v // v ∉ S}, x v.1))) := by
    simp only [hint]
    exact ENNReal.Tendsto.const_mul ((ENNReal.continuous_ofReal.tendsto _).comp hpq) (Or.inr hB)
  have hf0 : ∫⁻ y, f 0 y ∂I ≠ ⊤ := by
    rw [hint 0]
    exact ENNReal.mul_ne_top hB ENNReal.ofReal_ne_top
  have hI : ∫⁻ y, purePr σ J b S Ψinf Ψ y ∂I = ⨅ k, ∫⁻ y, f k y ∂I := by
    rw [← lintegral_iInf hfm hanti hf0]
    exact lintegral_congr fun y => (hinf y).symm
  rw [hI]
  exact tendsto_nhds_unique
    (tendsto_atTop_iInf fun k l hkl => lintegral_mono fun y => hanti hkl y) hlim

end Finite

theorem prim_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (I : Measure (Fin 1 → Fin (M + 2) → AF F ⊗[F] E)) (minf : Measure (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)), IsEulerProd b I 1 minf m → SigmaFinite minf → (∀ v, SigmaFinite (m v)) → ∀ S₁ : Finset (HeightOneSpectrum (𝓞 F)), (∀ v, v ∉ S₁ → primV σ J b v ⊆ latV b v ∧ MeasurableSet (primV σ J b v)) → Summable (fun v => |(m v (primV σ J b v)).toReal - 1|) → ∃ S₃ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₃ ⊆ S → ∀ (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable Ψinf → (∀ v, Measurable (Ψ v)) → ∫⁻ y, purePr σ J b S Ψinf Ψ y ∂I = ((∫⁻ y, Ψinf y ∂minf) * ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m v)) * ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (primV σ J b v.1)).toReal) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b I minf m hEu hsi hsv S₁ hprim hsumP
  classical
  obtain ⟨hlat, hsum, S₀, hE⟩ := hEu
  refine ⟨S₀ ∪ S₁, fun S hS Ψinf Ψ hΨinf hΨ => ?_⟩
  have hS₀ : S₀ ⊆ S := Finset.subset_union_left.trans hS
  have hS₁ : S₁ ⊆ S := Finset.subset_union_right.trans hS
  obtain ⟨gi, gim, gimono, gisup, gifin⟩ := exists_approx minf Ψinf hΨinf
  choose g gm gmono gsup gfin using fun v => @exists_approx _ _ (m v) (hsv v) (Ψ v) (hΨ v)
  let G : ℕ → (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞ :=
    fun k => purePr σ J b S (gi k) (fun v => g v k)
  have hGm : ∀ k, Measurable (G k) := fun k =>
    GlobalTheory.T.euler_product_lintegral_limit F E σ hσ M J hJ d b S _ _ (gim k) (fun v => gm v k)
  have hpm : ∀ (a : Fin 1 → Fin (M + 2) → AF F ⊗[F] E), Monotone fun k =>
      ∏ v ∈ S, g v k (projV v (projFin a)) := fun a k l hkl =>
    Finset.prod_le_prod' fun v _ => gmono v _ hkl
  have hGmono : Monotone G := by
    intro k l hkl y
    exact Set.indicator_le_indicator (mul_le_mul' (gimono _ hkl) (hpm y hkl))
  have hGsup : ∀ y, ⨆ k, G k y = purePr σ J b S Ψinf Ψ y := by
    intro y
    by_cases hy : ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v
    · have hmem : y ∈ {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E |
          ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v} := hy
      simp only [G, purePr, Set.indicator_of_mem hmem]
      rw [← iSup_mul_iSup_mono (gimono _) (hpm y), ← prod_iSup_mono S _ (fun v => gmono v _)]
      simp only [gisup, gsup]
    · have hmem : y ∉ {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E |
          ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v} := hy
      simp only [G, purePr, Set.indicator_of_notMem hmem]
      exact iSup_const
  have hIinf : ⨆ k, ∫⁻ y, gi k y ∂minf = ∫⁻ y, Ψinf y ∂minf := by
    rw [← lintegral_iSup gim (fun k l hkl y => gimono y hkl)]
    exact lintegral_congr gisup
  have hIv : ∀ v, ⨆ k, ∫⁻ y, g v k y ∂(m v) = ∫⁻ y, Ψ v y ∂(m v) := by
    intro v
    rw [← lintegral_iSup (gm v) (fun k l hkl y => gmono v y hkl)]
    exact lintegral_congr (gsup v)
  have hmi : Monotone fun k => ∫⁻ y, gi k y ∂minf := fun k l hkl =>
    lintegral_mono fun y => gimono y hkl
  have hmv : ∀ v, Monotone fun k => ∫⁻ y, g v k y ∂(m v) := fun v k l hkl =>
    lintegral_mono fun y => gmono v y hkl
  calc ∫⁻ y, purePr σ J b S Ψinf Ψ y ∂I = ∫⁻ y, ⨆ k, G k y ∂I :=
        lintegral_congr fun y => (hGsup y).symm
    _ = ⨆ k, ∫⁻ y, G k y ∂I := lintegral_iSup hGm hGmono
    _ = ⨆ k, ((∫⁻ y, gi k y ∂minf) * ∏ v ∈ S, ∫⁻ y, g v k y ∂(m v)) *
          ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (primV σ J b v.1)).toReal) :=
        iSup_congr fun k => finite_case σ hσ J b I minf m hlat hsum hE hprim hsumP hS₀ hS₁
          (gi k) (fun v => g v k) (gim k) (fun v => gm v k) (gifin k) (fun v _ => gfin v k)
    _ = (⨆ k, (∫⁻ y, gi k y ∂minf) * ∏ v ∈ S, ∫⁻ y, g v k y ∂(m v)) *
          ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (primV σ J b v.1)).toReal) :=
        (ENNReal.iSup_mul ..).symm
    _ = _ := by
        rw [← iSup_mul_iSup_mono hmi
          (fun k l hkl => Finset.prod_le_prod' fun v _ => hmv v hkl),
          ← prod_iSup_mono S _ hmv, hIinf]
        simp only [hIv]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimFormula
