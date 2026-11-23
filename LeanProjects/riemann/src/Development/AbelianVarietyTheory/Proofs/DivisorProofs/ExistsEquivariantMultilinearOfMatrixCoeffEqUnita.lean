import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem eq_zero_of_mem_closure_span_of_inner_eq_zero {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] {s : Set K} {z : K} (hz : z ∈ closure (Submodule.span ℂ s : Set K))
    (h : ∀ w ∈ s, ⟪w, z⟫_ℂ = 0) : z = 0 := by
  have h1 : ∀ w ∈ Submodule.span ℂ s, ⟪w, z⟫_ℂ = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
  have h2 : closure (Submodule.span ℂ s : Set K) ⊆ {w | ⟪w, z⟫_ℂ = 0} :=
    closure_minimal h1 (isClosed_eq (by fun_prop) (by fun_prop))
  exact inner_self_eq_zero.1 (h2 hz)

theorem exists_vector_of_inner_eq_prod {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type}
    [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)]
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {A : ι → Type} (e : ∀ τ, A τ → H τ) (f : (∀ τ, A τ) → K) (c : ℝ)
    (hd : ∀ τ, Dense (Submodule.span ℂ (Set.range (e τ)) : Set (H τ)))
    (hf : ∀ a b, ⟪f a, f b⟫_ℂ = (c : ℂ) * ∏ τ, ⟪e τ (a τ), e τ (b τ)⟫_ℂ) (y : ∀ τ, H τ) :
    ∃ z ∈ closure (Submodule.span ℂ (Set.range f) : Set K),
      (∀ a, ⟪f a, z⟫_ℂ = (c : ℂ) * ∏ τ, ⟪e τ (a τ), y τ⟫_ℂ) ∧
        ⟪z, z⟫_ℂ = (c : ℂ) * ∏ τ, ⟪y τ, y τ⟫_ℂ := by
  classical
  let B : (∀ τ, H τ) → (∀ τ, H τ) → ℂ := fun p q => (c : ℂ) * ∏ τ, ⟪p τ, q τ⟫_ℂ
  have hBc : Continuous fun p : (∀ τ, H τ) × (∀ τ, H τ) => B p.1 p.2 := by
    simp only [B]; fun_prop
  let lin : (∀ τ, A τ →₀ ℂ) → (∀ τ, H τ) := fun x τ => Finsupp.linearCombination ℂ (e τ) (x τ)
  let P : (∀ τ, A τ →₀ ℂ) → K := fun x =>
    ∑ a ∈ Fintype.piFinset (fun τ => (x τ).support), (∏ τ, x τ (a τ)) • f a
  have hPmem : ∀ x, P x ∈ Submodule.span ℂ (Set.range f) := fun x =>
    Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h1 : ∀ x (z : K) (q : ∀ τ, H τ), (∀ a, ⟪f a, z⟫_ℂ = B (fun τ => e τ (a τ)) q) →
      ⟪P x, z⟫_ℂ = B (lin x) q := by
    intro x z q hz
    simp only [P, B, lin, sum_inner, inner_smul_left, hz, Finsupp.linearCombination_apply, Finsupp.sum]
    rw [Finset.prod_univ_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.prod_mul_distrib, map_prod]
    ring
  have hconj : ∀ p q, (starRingEnd ℂ) (B p q) = B q p := by
    intro p q
    simp only [B, map_mul, map_prod, inner_conj_symm, Complex.conj_ofReal]
  have h2 : ∀ x a, ⟪f a, P x⟫_ℂ = B (fun τ => e τ (a τ)) (lin x) := by
    intro x a
    rw [← inner_conj_symm, h1 x (f a) (fun τ => e τ (a τ)) (fun b => hf b a), hconj]
  have h3 : ∀ x x', ⟪P x, P x'⟫_ℂ = B (lin x) (lin x') := fun x x' => h1 x _ _ (h2 x')
  have hdl : DenseRange lin := by
    have : DenseRange (Pi.map fun τ => fun x : A τ →₀ ℂ => Finsupp.linearCombination ℂ (e τ) x) := by
      refine DenseRange.piMap fun τ => ?_
      have := hd τ
      rw [← Finsupp.range_linearCombination, LinearMap.coe_range] at this
      exact this
    exact this
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (hdl y)
  choose x hx using hu
  have hlim' : Filter.Tendsto (fun n => lin (x n)) Filter.atTop (nhds y) := by
    simpa only [hx] using hlim
  have hcau : CauchySeq fun n => P (x n) := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    let G : (∀ τ, H τ) × (∀ τ, H τ) → ℝ := fun p =>
      Real.sqrt (B p.1 p.1 - B p.1 p.2 - B p.2 p.1 + B p.2 p.2).re
    have hG : Continuous G := by
      simp only [G, B]; fun_prop
    have hG0 : G (y, y) = 0 := by simp [G]
    have ht : Filter.Tendsto (fun n : ℕ × ℕ => (lin (x n.1), lin (x n.2))) Filter.atTop (nhds (y, y)) := by
      rw [← Filter.prod_atTop_atTop_eq]
      exact (hlim'.comp Filter.tendsto_fst).prodMk_nhds (hlim'.comp Filter.tendsto_snd)
    have := (hG.tendsto (y, y)).comp ht
    rw [hG0] at this
    refine this.congr fun n => ?_
    simp only [Function.comp, G]
    rw [dist_eq_norm, @norm_eq_sqrt_re_inner ℂ, inner_sub_sub_self, h3, h3, h3, h3]
    rfl
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcau
  have h4 : ∀ a, ⟪f a, z⟫_ℂ = B (fun τ => e τ (a τ)) y := by
    intro a
    have t1 : Filter.Tendsto (fun n => ⟪f a, P (x n)⟫_ℂ) Filter.atTop (nhds ⟪f a, z⟫_ℂ) :=
      Filter.Tendsto.inner tendsto_const_nhds hz
    have t2 := (hBc.tendsto (fun τ => e τ (a τ), y)).comp (tendsto_const_nhds.prodMk_nhds hlim')
    refine tendsto_nhds_unique t1 (t2.congr fun n => ?_)
    rw [h2]; rfl
  refine ⟨z, mem_closure_of_tendsto hz (Filter.Eventually.of_forall fun n => hPmem _), h4, ?_⟩
  have t1 : Filter.Tendsto (fun n => ⟪P (x n), z⟫_ℂ) Filter.atTop (nhds ⟪z, z⟫_ℂ) :=
    Filter.Tendsto.inner hz tendsto_const_nhds
  have t2 := (hBc.tendsto (y, y)).comp (hlim'.prodMk_nhds tendsto_const_nhds)
  refine tendsto_nhds_unique t1 (t2.congr fun n => ?_)
  rw [h1 _ _ _ h4]; rfl

theorem exists_continuousMultilinearMap_of_inner_eq_prod {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type}
    [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)]
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {A : ι → Type} (e : ∀ τ, A τ → H τ) (f : (∀ τ, A τ) → K) (c : ℝ)
    (hd : ∀ τ, Dense (Submodule.span ℂ (Set.range (e τ)) : Set (H τ)))
    (hf : ∀ a b, ⟪f a, f b⟫_ℂ = (c : ℂ) * ∏ τ, ⟪e τ (a τ), e τ (b τ)⟫_ℂ) :
    ∃ Φ : ContinuousMultilinearMap ℂ H K, ∀ y, Φ y ∈ closure (Submodule.span ℂ (Set.range f) : Set K) ∧
      ∀ a, ⟪f a, Φ y⟫_ℂ = (c : ℂ) * ∏ τ, ⟪e τ (a τ), y τ⟫_ℂ := by
  choose F hF1 hF2 hF3 using exists_vector_of_inner_eq_prod e f c hd hf
  let L : (∀ τ, A τ) → MultilinearMap ℂ H ℂ := fun a =>
    (c : ℂ) • (MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap fun τ => innerₛₗ ℂ (e τ (a τ))
  have hL : ∀ a y, ⟪f a, F y⟫_ℂ = L a y := by
    intro a y
    rw [hF2]; simp [L]
  have hmem : ∀ y, F y ∈ (Submodule.span ℂ (Set.range f)).topologicalClosure := hF1
  let M : MultilinearMap ℂ H K :=
    { toFun := F
      map_update_add' := by
        intro _ m i p q
        rw [← sub_eq_zero]
        refine eq_zero_of_mem_closure_span_of_inner_eq_zero (s := Set.range f)
          (Submodule.sub_mem _ (hmem _) (Submodule.add_mem _ (hmem _) (hmem _))) ?_
        rintro _ ⟨a, rfl⟩
        rw [inner_sub_right, inner_add_right, hL, hL, hL, MultilinearMap.map_update_add, sub_self]
      map_update_smul' := by
        intro _ m i r p
        rw [← sub_eq_zero]
        refine eq_zero_of_mem_closure_span_of_inner_eq_zero (s := Set.range f)
          (Submodule.sub_mem _ (hmem _) (Submodule.smul_mem _ _ (hmem _))) ?_
        rintro _ ⟨a, rfl⟩
        rw [inner_sub_right, inner_smul_right, hL, hL, MultilinearMap.map_update_smul, smul_eq_mul, sub_self] }
  refine ⟨M.mkContinuous (Real.sqrt |c|) fun y => ?_, fun y => ⟨hF1 y, hF2 y⟩⟩
  change ‖F y‖ ≤ _
  have h := congrArg norm (hF3 y)
  simp only [inner_self_eq_norm_sq_to_K, norm_mul, norm_prod, norm_pow, Complex.coe_algebraMap,
    Complex.norm_real, norm_norm, Real.norm_eq_abs, Finset.prod_pow] at h
  refine le_of_eq ?_
  refine (pow_left_inj₀ (n := 2) (by positivity) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt (abs_nonneg c)]
  simpa using h

set_option maxHeartbeats 800000 in

theorem exists_equivariant_multilinear_of_matrixCoeff_eq :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (H : ι → Type) [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)] [∀ τ, CompleteSpace (H τ)] (σ : ∀ τ, Mt n → (H τ →L[ℂ] H τ)) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : (ι → Mt n) → (K →L[ℂ] K)) (v : ∀ τ, H τ) (k : K), (∀ τ, (Hm τ).det ≠ 0 ∧ IsURepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ) ∧ IsIrredOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ) ∧ ‖v τ‖ = 1) → ρ 1 = 1 → (∀ u ∈ UG Hm, ∀ u' ∈ UG Hm, ρ (u * u') = ρ u * ρ u') → (∀ u ∈ UG Hm, ∀ y, ‖ρ u y‖ = ‖y‖) → (∀ u ∈ UG Hm, ⟪k, ρ u k⟫_ℂ = ((‖k‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ) → ∃ Φ : ContinuousMultilinearMap ℂ H K, Φ v = k ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (Hm τ), ∀ y, Φ (Function.update y τ (σ τ g (y τ))) = ρ (Pi.mulSingle τ g) (Φ y)) ∧ ∀ y, Φ y ∈ closure (Submodule.span ℂ {z | ∃ u ∈ UG Hm, z = ρ u k} : Set K) := by
  intro n ι _ _ Hm H _ _ _ σ K _ _ _ ρ v k hσ hρ1 hρm hρn hco
  have hone : ∀ τ, (1 : Mt n) ∈ Formalism.QuantumDeterminants.UH (Hm τ) := fun τ => by simp [Formalism.QuantumDeterminants.UH]
  have hmul : ∀ τ, ∀ a ∈ Formalism.QuantumDeterminants.UH (Hm τ), ∀ b ∈ Formalism.QuantumDeterminants.UH (Hm τ), a * b ∈ Formalism.QuantumDeterminants.UH (Hm τ) := by
    intro τ a ha b hb
    simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at ha hb ⊢
    rw [conjTranspose_mul]
    calc bᴴ * aᴴ * Hm τ * (a * b) = bᴴ * (aᴴ * Hm τ * a) * b := by simp only [Matrix.mul_assoc]
      _ = Hm τ := by rw [ha, hb]
  have hinv : ∀ τ, ∀ a ∈ Formalism.QuantumDeterminants.UH (Hm τ), ∃ b ∈ Formalism.QuantumDeterminants.UH (Hm τ), a * b = 1 := by
    intro τ a ha
    simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at ha ⊢
    have hd : IsUnit a.det := by
      have := congrArg Matrix.det ha
      rw [det_mul, det_mul] at this
      refine isUnit_iff_ne_zero.2 fun h => (hσ τ).1 ?_
      rw [← this, h, mul_zero]
    refine ⟨a⁻¹, ?_, Matrix.mul_nonsing_inv a hd⟩
    calc a⁻¹ᴴ * Hm τ * a⁻¹ = a⁻¹ᴴ * (aᴴ * Hm τ * a) * a⁻¹ := by rw [ha]
      _ = (a * a⁻¹)ᴴ * Hm τ * (a * a⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Hm τ := by rw [Matrix.mul_nonsing_inv a hd]; simp
  have hσ1 : ∀ τ, σ τ 1 = 1 := fun τ => (hσ τ).2.1.1.1
  have hσm : ∀ τ, ∀ a ∈ Formalism.QuantumDeterminants.UH (Hm τ), ∀ b ∈ Formalism.QuantumDeterminants.UH (Hm τ), σ τ (a * b) = σ τ a * σ τ b :=
    fun τ => (hσ τ).2.1.1.2
  have hσi : ∀ τ, ∀ a ∈ Formalism.QuantumDeterminants.UH (Hm τ), ∀ p q, ⟪σ τ a p, σ τ a q⟫_ℂ = ⟪p, q⟫_ℂ := fun τ a ha =>
    (LinearMap.norm_map_iff_inner_map_map (σ τ a)).1 ((hσ τ).2.1.2.1 a ha)
  have hρi : ∀ a ∈ UG Hm, ∀ p q, ⟪ρ a p, ρ a q⟫_ℂ = ⟪p, q⟫_ℂ := fun a ha =>
    (LinearMap.norm_map_iff_inner_map_map (ρ a)).1 (hρn a ha)

  have hdiv : ∀ a ∈ UG Hm, ∀ b ∈ UG Hm, ∃ d ∈ UG Hm, a * d = b := by
    intro a ha b hb
    choose a' h1 h2 using fun τ => hinv τ (a τ) (ha τ)
    refine ⟨a' * b, fun τ => hmul τ _ (h1 τ) _ (hb τ), funext fun τ => ?_⟩
    simp only [Pi.mul_apply]
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  let e : ∀ τ, Formalism.QuantumDeterminants.UH (Hm τ) → H τ := fun τ g => σ τ g (v τ)
  let f : (∀ τ, Formalism.QuantumDeterminants.UH (Hm τ)) → K := fun a => ρ (fun τ => a τ) k
  have hrange : Set.range f = {z | ∃ u ∈ UG Hm, z = ρ u k} := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨fun τ => a τ, fun τ => (a τ).2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun τ => ⟨u τ, hu τ⟩, rfl⟩
  have hd : ∀ τ, Dense (Submodule.span ℂ (Set.range (e τ)) : Set (H τ)) := by
    intro τ
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    have hst : ∀ g ∈ Formalism.QuantumDeterminants.UH (Hm τ), ∀ w ∈ (Submodule.span ℂ (Set.range (e τ))).topologicalClosure,
        σ τ g w ∈ (Submodule.span ℂ (Set.range (e τ))).topologicalClosure := by
      intro g hg w hw
      refine map_mem_closure (σ τ g).continuous hw fun p hp => ?_
      have : Submodule.span ℂ (Set.range (e τ)) ≤
          (Submodule.span ℂ (Set.range (e τ))).comap (σ τ g).toLinearMap := by
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        refine Submodule.subset_span ⟨⟨g * b, hmul τ _ hg _ b.2⟩, ?_⟩
        simp only [e]
        rw [hσm τ _ hg _ b.2]; rfl
      exact this hp
    refine ((hσ τ).2.2.1 _ (Submodule.isClosed_topologicalClosure _) hst).resolve_left fun h => ?_
    have hv : v τ ∈ (Submodule.span ℂ (Set.range (e τ))).topologicalClosure :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨1, hone τ⟩, by simp [e, hσ1]⟩)
    rw [h, Submodule.mem_bot] at hv
    have := (hσ τ).2.2.2
    rw [hv, norm_zero] at this
    exact zero_ne_one this
  have hf : ∀ a b, ⟪f a, f b⟫_ℂ = ((‖k‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪e τ (a τ), e τ (b τ)⟫_ℂ := by
    intro a b
    have ha : (fun τ => (a τ : Mt n)) ∈ UG Hm := fun τ => (a τ).2
    obtain ⟨d, hdm, hd⟩ := hdiv _ ha (fun τ => (b τ : Mt n)) (fun τ => (b τ).2)
    simp only [f, e]
    rw [← hd, hρm _ ha _ hdm, ContinuousLinearMap.mul_apply, hρi _ ha, hco d hdm]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    have : (b τ : Mt n) = a τ * d τ := (congrFun hd τ).symm
    rw [this, hσm τ _ (a τ).2 _ (hdm τ), ContinuousLinearMap.mul_apply, hσi τ _ (a τ).2]
  obtain ⟨Φ, hΦ⟩ := exists_continuousMultilinearMap_of_inner_eq_prod e f _ hd hf
  have hmem : ∀ y, Φ y ∈ (Submodule.span ℂ (Set.range f)).topologicalClosure := fun y => (hΦ y).1
  have hk : f (fun τ => ⟨1, hone τ⟩) = k := by
    change ρ 1 k = k
    rw [hρ1]; rfl
  refine ⟨Φ, ?_, fun τ g hg y => ?_, fun y => hrange ▸ (hΦ y).1⟩
  · rw [← sub_eq_zero]
    refine eq_zero_of_mem_closure_span_of_inner_eq_zero (s := Set.range f)
      (Submodule.sub_mem _ (hmem _) (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, hk⟩))) ?_
    rintro _ ⟨a, rfl⟩
    rw [inner_sub_right, (hΦ v).2, ← hk, hf, hk]
    simp [e, hσ1]
  · have hs : (Pi.mulSingle τ g : ι → Mt n) ∈ UG Hm := by
      intro τ'
      by_cases h : τ' = τ
      · subst h; simpa using hg
      · rw [Pi.mulSingle_eq_of_ne h]; exact hone τ'
    have hst : ρ (Pi.mulSingle τ g) (Φ y) ∈ (Submodule.span ℂ (Set.range f)).topologicalClosure := by
      refine map_mem_closure (ρ _).continuous (hmem y) fun p hp => ?_
      have : Submodule.span ℂ (Set.range f) ≤
          (Submodule.span ℂ (Set.range f)).comap (ρ (Pi.mulSingle τ g)).toLinearMap := by
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        have hb : (fun τ => (b τ : Mt n)) ∈ UG Hm := fun τ => (b τ).2
        refine Submodule.subset_span ?_
        rw [hrange]
        have hsb : ((Pi.mulSingle τ g : ι → Mt n) * fun τ => (b τ : Mt n)) ∈ UG Hm := by
          intro τ'
          rw [Pi.mul_apply]
          exact hmul τ' _ (hs τ') _ (hb τ')
        refine ⟨_, hsb, ?_⟩
        rw [hρm _ hs _ hb]; rfl
      exact this hp
    rw [← sub_eq_zero]
    refine eq_zero_of_mem_closure_span_of_inner_eq_zero (s := Set.range f)
      (Submodule.sub_mem _ (hmem _) hst) ?_
    rintro _ ⟨a, rfl⟩
    have ha : (fun τ => (a τ : Mt n)) ∈ UG Hm := fun τ => (a τ).2
    obtain ⟨d, hdm, hd⟩ := hdiv _ hs _ ha
    have h1 : f a = ρ (Pi.mulSingle τ g) (f fun τ => ⟨d τ, hdm τ⟩) := by
      simp only [f]
      rw [← hd, hρm _ hs _ hdm]; rfl
    rw [inner_sub_right, (hΦ _).2, h1, hρi _ hs, (hΦ _).2, sub_eq_zero]
    congr 1
    refine Finset.prod_congr rfl fun τ' _ => ?_
    have h2 : (a τ' : Mt n) = (Pi.mulSingle τ g : ι → Mt n) τ' * d τ' := (congrFun hd τ').symm
    simp only [e]
    rw [h2]
    by_cases h : τ' = τ
    · subst h
      rw [Pi.mulSingle_eq_same, Function.update_self, hσm _ _ hg _ (hdm _), ContinuousLinearMap.mul_apply, hσi _ _ hg]
    · rw [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h, Matrix.one_mul]

end GlobalTheory
