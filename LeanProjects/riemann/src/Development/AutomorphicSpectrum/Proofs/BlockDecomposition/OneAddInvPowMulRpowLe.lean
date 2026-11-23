import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
import GroundTheory.GlobalFields.TateThesis.TateMain
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAdeleWeight
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtra
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.EpConvB

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup PositivityTheory.RgEis

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem integrable_weight {σ : ℝ} (hσ : 1 < σ) : ∃ A₀ : ℕ, ∀ (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ), A₀ ≤ A →
    Integrable (fun t : IdeleGroup K ↦ adeleWeight L A (t : 𝔸[K]) * (ideleModule K t : ℝ) ^ σ)
      (ideleMeasure K) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * σ + 2 < k := exists_nat_gt _
  refine ⟨Fintype.card (InfinitePlace K) * k, fun L A hA ↦ ?_⟩
  refine (integrable_zetaBound hσ hk L).mono'
    (((continuous_adeleWeight L A).comp Units.continuous_val).mul
      (continuous_ideleModule_val.rpow_const fun _ ↦ Or.inr (by linarith))).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ ?_)
  have hpow : 0 ≤ (ideleModule K x : ℝ) ^ σ := Real.rpow_nonneg (ideleModule K x).2.le σ
  rw [Real.norm_of_nonneg (mul_nonneg (adeleWeight_nonneg _ _ _) hpow)]
  set a := toInfinite K x
  set b := toFinite K x
  have hI := infiniteZetaBound_nonneg σ k a
  by_cases hb : (b : FiniteAdeleRing (𝓞 K) K) ∈ idealFiniteAdeles L
  · have hfz : finiteZetaBound L σ b = finiteModule (ofFinite b) ^ σ := by
      rw [finiteZetaBound, if_pos hb]
    have hb' : (x : 𝔸[K]).2 ∈ idealFiniteAdeles L := hb
    have hw : adeleWeight L A (x : 𝔸[K]) = ((1 + ‖homeomorphMixedSpace K (x : 𝔸[K]).1‖) ^ A)⁻¹ := by
      unfold adeleWeight
      rw [if_pos hb']
    rw [hfz, ideleModule_rpow_eq, hw]
    set y := homeomorphMixedSpace K (x : 𝔸[K]).1
    have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
    have hF : 0 ≤ finiteModule (ofFinite b) ^ σ := by
      have := finiteModule_pos (ofFinite b)
      positivity
    have hP : 0 ≤ ∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ) :=
      Finset.prod_nonneg fun w _ ↦ by positivity
    have hq : ∏ w, (1 + ‖(a : InfiniteAdeleRing K) w‖) ^ k ≤ (1 + ‖y‖) ^ A := by
      calc ∏ w, (1 + ‖(a : InfiniteAdeleRing K) w‖) ^ k
          ≤ ∏ _w : InfinitePlace K, (1 + ‖y‖) ^ k :=
            Finset.prod_le_prod (fun w _ ↦ by positivity) fun w _ ↦
              pow_le_pow_left₀ (by positivity)
                (by
                  have h : ‖(a : InfiniteAdeleRing K) w‖ ≤ ‖y‖ :=
                    norm_le_norm_homeomorphMixedSpace (x : 𝔸[K]).1 w
                  linarith) k
        _ = (1 + ‖y‖) ^ (Fintype.card (InfinitePlace K) * k) := by
            rw [Finset.prod_const, Finset.card_univ, ← pow_mul, mul_comm]
        _ ≤ (1 + ‖y‖) ^ A := pow_le_pow_right₀ (by linarith) hA
    have hq0 : 0 < ∏ w, (1 + ‖(a : InfiniteAdeleRing K) w‖) ^ k :=
      Finset.prod_pos fun w _ ↦ by positivity
    have hinf : infiniteZetaBound σ k a = (∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ)) /
        ∏ w, (1 + ‖(a : InfiniteAdeleRing K) w‖) ^ k := by
      rw [infiniteZetaBound, Finset.prod_div_distrib]
    rw [hinf]
    calc ((1 + ‖y‖) ^ A)⁻¹ * ((∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ)) *
          finiteModule (ofFinite b) ^ σ)
        ≤ (∏ w, (1 + ‖(a : InfiniteAdeleRing K) w‖) ^ k)⁻¹ *
          ((∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ)) *
            finiteModule (ofFinite b) ^ σ) :=
          mul_le_mul_of_nonneg_right (inv_anti₀ hq0 hq) (mul_nonneg hP hF)
      _ = _ := by rw [div_eq_mul_inv]; ring
  · have hb' : (x : 𝔸[K]).2 ∉ idealFiniteAdeles L := hb
    have hw : adeleWeight L A (x : 𝔸[K]) = 0 := by
      unfold adeleWeight
      rw [if_neg hb']
    rw [hw, zero_mul]
    exact mul_nonneg hI (finiteZetaBound_nonneg _ _ _)

theorem continuous_inv_entry (i j : ι) :
    Continuous fun h : GL ι 𝔸[K] ↦ ((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) i j := by
  have h : Continuous fun h : GL ι 𝔸[K] ↦ ((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) :=
    Units.continuous_val.comp continuous_inv
  exact h.matrix_elem i j

theorem inv_mulVec_mulVec (m : GL ι 𝔸[K]) (y : ι → 𝔸[K]) :
    ((m⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) *ᵥ ((m : Matrix ι ι 𝔸[K]) *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem fin_mulVec (M : Matrix ι ι 𝔸[K]) (z : ι → 𝔸[K]) (i : ι) :
    ((M *ᵥ z) i).2 = ∑ j, Adele2.finRingHom (M i j) * (z j).2 := by
  show Adele2.finRingHom (∑ j, M i j * z j) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ map_mul _ _ _

theorem inf_mulVec (M : Matrix ι ι 𝔸[K]) (z : ι → 𝔸[K]) (i : ι) :
    homeomorphMixedSpace K ((M *ᵥ z) i).1 =
      ∑ j, Adele2.infRingHom (M i j) * homeomorphMixedSpace K (z j).1 := by
  show Adele2.infRingHom (∑ j, M i j * z j) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ map_mul _ _ _

theorem majorant_tensor (φ : 𝓢(ι → mixedSpace K, ℂ)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (b : ι → 𝔸ᶠ[K]) {C : Set (GL ι 𝔸[K])} (hC : IsCompact C) (A : ℕ) :
    ∃ (M : ℝ) (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ), 0 ≤ M ∧ ∀ m ∈ C, ∀ y : ι → 𝔸[K],
      ‖GJMatrix.schwartzBruhatTensorPi φ (GJMatrix.finiteTensor fun i ↦ cosetIndicator I (b i))
        ((m : Matrix ι ι 𝔸[K]) *ᵥ y)‖ ≤ M * ∏ i, adeleWeight L A (y i) := by
  set B : Set (ι → 𝔸ᶠ[K]) :=
    Set.pi Set.univ fun i ↦ b i +ᵥ (idealFiniteAdeles I : Set 𝔸ᶠ[K])
  have hB : IsCompact B := isCompact_univ_pi fun i ↦ (isCompact_idealFiniteAdeles I).vadd (b i)
  let T : GL ι 𝔸[K] × (ι → 𝔸ᶠ[K]) → ι → 𝔸ᶠ[K] := fun p i ↦
    ∑ j, Adele2.finRingHom (((p.1⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) i j) * p.2 j
  have hfc : Continuous (Adele2.finRingHom (K := K)) := continuous_snd
  have hic : Continuous (Adele2.infRingHom (K := K)) :=
    (homeomorphMixedSpace K).continuous.comp continuous_fst
  have hT : Continuous T := continuous_pi fun i ↦ continuous_finset_sum _ fun j _ ↦
    (hfc.comp ((continuous_inv_entry i j).comp continuous_fst)).mul
      ((continuous_apply j).comp continuous_snd)
  set S : Set 𝔸ᶠ[K] := ⋃ i : ι, (fun x : ι → 𝔸ᶠ[K] ↦ x i) '' (T '' (C ×ˢ B))
  have hS : IsCompact S := isCompact_iUnion fun i ↦
    ((hC.prod hB).image hT).image (continuous_apply i)
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles hS
  have hfin : ∀ m ∈ C, ∀ y : ι → 𝔸[K],
      (∀ i, GJMatrix.finPartPi ((m : Matrix ι ι 𝔸[K]) *ᵥ y) i - b i ∈ idealFiniteAdeles I) →
      ∀ i, (y i).2 ∈ idealFiniteAdeles L := by
    intro m hm y hy i
    refine hL (Set.mem_iUnion.2 ⟨i, _, ⟨(m, GJMatrix.finPartPi ((m : Matrix ι ι 𝔸[K]) *ᵥ y)),
      ⟨hm, fun j _ ↦ mem_vadd_idealFiniteAdeles.2 (hy j)⟩, rfl⟩, ?_⟩)
    have h := fin_mulVec ((m⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) ((m : Matrix ι ι 𝔸[K]) *ᵥ y) i
    rw [inv_mulVec_mulVec] at h
    exact h.symm
  let c : GL ι 𝔸[K] → ℝ := fun h ↦ ∑ i, ∑ j,
    ‖Adele2.infRingHom (((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) i j)‖
  have hc : Continuous c := continuous_finset_sum _ fun i _ ↦ continuous_finset_sum _ fun j _ ↦
    (hic.comp (continuous_inv_entry i j)).norm
  obtain ⟨D, hD⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  set D' := max D 1
  have hD1 : 1 ≤ D' := le_max_right _ _
  have hD0 : 0 < D' := zero_lt_one.trans_le hD1
  set N := Fintype.card ι
  obtain ⟨P, hP, hφ⟩ := GroundTheory.Global.exists_norm_le_inv_one_add_pow φ (N * A)
  refine ⟨P * D' ^ (N * A), L, by positivity, fun m hm y ↦ ?_⟩
  have hR0 : 0 ≤ P * D' ^ (N * A) * ∏ i, adeleWeight L A (y i) :=
    mul_nonneg (by positivity) (Finset.prod_nonneg fun _ _ ↦ adeleWeight_nonneg _ _ _)
  set Y := (m : Matrix ι ι 𝔸[K]) *ᵥ y
  simp only [GJMatrix.schwartzBruhatTensorPi, GJMatrix.finiteTensor, cosetIndicator_apply,
    Finset.prod_boole, Finset.mem_univ, true_implies]
  by_cases hm' : ∀ i, GJMatrix.finPartPi Y i - b i ∈ idealFiniteAdeles I
  · rw [if_pos hm', mul_one]
    have hy := hfin m hm y hm'
    set z := GJMatrix.infPartPi Y
    have hcD : c m ≤ D' := (le_abs_self _).trans
      (((Real.norm_eq_abs _).symm.trans_le (hD m hm)).trans (le_max_left _ _))
    have hyz : ∀ i, ‖homeomorphMixedSpace K (y i).1‖ ≤ D' * ‖z‖ := by
      intro i
      have h := inf_mulVec ((m⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) Y i
      rw [inv_mulVec_mulVec] at h
      rw [h]
      have h1 : ∀ j, ‖Adele2.infRingHom (((m⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) i j) *
          homeomorphMixedSpace K (Y j).1‖ ≤
          ‖Adele2.infRingHom (((m⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) i j)‖ * ‖z‖ := fun j ↦
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm z j) (norm_nonneg _))
      have h2 : ∑ j, ‖Adele2.infRingHom (((m⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) i j)‖ ≤ c m :=
        Finset.single_le_sum (f := fun i ↦ ∑ j,
          ‖Adele2.infRingHom (((m⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) i j)‖)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)
      calc _ ≤ ∑ j, ‖Adele2.infRingHom (((m⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) i j) *
            homeomorphMixedSpace K (Y j).1‖ := norm_sum_le _ _
        _ ≤ ∑ j, ‖Adele2.infRingHom (((m⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) i j)‖ * ‖z‖ :=
            Finset.sum_le_sum fun j _ ↦ h1 j
        _ = (∑ j, ‖Adele2.infRingHom (((m⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) i j)‖) * ‖z‖ := by
            rw [Finset.sum_mul]
        _ ≤ D' * ‖z‖ := mul_le_mul_of_nonneg_right (h2.trans hcD) (norm_nonneg _)
    set t := D' * (1 + ‖z‖)
    have ht : 0 < t := by positivity
    have hw : ∀ i, (t ^ A)⁻¹ ≤ adeleWeight L A (y i) := by
      intro i
      have h0 := norm_nonneg (homeomorphMixedSpace K (y i).1)
      have hle : 1 + ‖homeomorphMixedSpace K (y i).1‖ ≤ t := by
        have : t = D' + D' * ‖z‖ := by simp only [t]; ring
        linarith [hyz i]
      unfold adeleWeight
      rw [if_pos (hy i)]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hle A)
    have hprod : (t ^ (N * A))⁻¹ ≤ ∏ i, adeleWeight L A (y i) := by
      calc (t ^ (N * A))⁻¹ = ∏ _i : ι, (t ^ A)⁻¹ := by
            rw [Finset.prod_const, Finset.card_univ, inv_pow, ← pow_mul, mul_comm]
        _ ≤ _ := Finset.prod_le_prod (fun _ _ ↦ by positivity) fun i _ ↦ hw i
    calc ‖φ z‖ ≤ P * ((1 + ‖z‖) ^ (N * A))⁻¹ := hφ z
      _ = P * D' ^ (N * A) * (t ^ (N * A))⁻¹ := by
          have hz : (1 + ‖z‖) ^ (N * A) ≠ 0 := by positivity
          have hD : D' ^ (N * A) ≠ 0 := by positivity
          simp only [t, mul_pow]
          field_simp
      _ ≤ P * D' ^ (N * A) * ∏ i, adeleWeight L A (y i) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
  · rw [if_neg hm', mul_zero, norm_zero]
    exact hR0

theorem exists_majorant {Ψ : (ι → 𝔸[K]) → ℂ} (hΨ : Ψ ∈ GJMatrix.schwartzBruhatPi K ι)
    {C : Set (GL ι 𝔸[K])} (hC : IsCompact C) (A : ℕ) :
    ∃ (M : ℝ) (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ), 0 ≤ M ∧ ∀ m ∈ C, ∀ y : ι → 𝔸[K],
      ‖Ψ ((m : Matrix ι ι 𝔸[K]) *ᵥ y)‖ ≤ M * ∏ i, adeleWeight L A (y i) := by
  rw [GJMatrix.schwartzBruhatPi_eq_cosetSpanPi] at hΨ
  induction hΨ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, I, b, rfl⟩ := hG
    exact majorant_tensor φ I b hC A
  | zero =>
    exact ⟨0, 1, le_rfl, fun _ _ _ ↦ by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨M₁, L₁, h₁, hb₁⟩ := hG
    obtain ⟨M₂, L₂, h₂, hb₂⟩ := hH
    set L := fractionalIdealSupUnit L₁ L₂
    have hmono : ∀ {L' : (FractionalIdeal (𝓞 K)⁰ K)ˣ}, (L' : FractionalIdeal (𝓞 K)⁰ K) ≤ L →
        ∀ y : ι → 𝔸[K], ∏ i, adeleWeight L' A (y i) ≤ ∏ i, adeleWeight L A (y i) := fun h y ↦
      Finset.prod_le_prod (fun _ _ ↦ adeleWeight_nonneg _ _ _) fun i _ ↦ adeleWeight_mono h A _
    refine ⟨M₁ + M₂, L, add_nonneg h₁ h₂, fun m hm y ↦ ?_⟩
    calc ‖(G + H) ((m : Matrix ι ι 𝔸[K]) *ᵥ y)‖
        ≤ ‖G ((m : Matrix ι ι 𝔸[K]) *ᵥ y)‖ + ‖H ((m : Matrix ι ι 𝔸[K]) *ᵥ y)‖ := norm_add_le _ _
      _ ≤ M₁ * ∏ i, adeleWeight L₁ A (y i) + M₂ * ∏ i, adeleWeight L₂ A (y i) :=
          add_le_add (hb₁ m hm y) (hb₂ m hm y)
      _ ≤ M₁ * ∏ i, adeleWeight L A (y i) + M₂ * ∏ i, adeleWeight L A (y i) :=
          add_le_add (mul_le_mul_of_nonneg_left (hmono le_sup_left y) h₁)
            (mul_le_mul_of_nonneg_left (hmono le_sup_right y) h₂)
      _ = _ := by ring
  | smul r G _ hG =>
    obtain ⟨M, L, hM, hb⟩ := hG
    refine ⟨‖r‖ * M, L, by positivity, fun m hm y ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb m hm y) (norm_nonneg r)

theorem packing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {A : ℕ}
    (hA : Module.finrank ℝ E < A) (hd : 0 < Module.finrank ℝ E) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ η : ℝ, 0 < η → ∀ F : Finset E,
      (∀ y ∈ F, ∀ y' ∈ F, y ≠ y' → η ≤ ‖y - y'‖ ^ Module.finrank ℝ E) →
      ∑ y ∈ F, ((1 + ‖y‖) ^ A)⁻¹ ≤ c * (1 + η⁻¹) :=
  _root_.UpperTheory.Reformulated.B.DYga2.main μ hA hd

theorem exists_finiteModule_le (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ c : ℝ, 0 < c ∧ ∀ τ : IdeleGroup K, (τ : 𝔸[K]).2 ∈ idealFiniteAdeles L → finiteModule τ ≤ c := by
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact (isCompact_idealFiniteAdeles L)
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  set u : Kˣ := Units.mk0 _ hdK
  have hu : 0 < finiteModule (diagonal K u) := finiteModule_pos _
  refine ⟨(finiteModule (diagonal K u))⁻¹, by positivity, fun τ hτ ↦ ?_⟩
  have h1 : finiteModule (diagonal K u * τ) ≤ 1 := by
    rw [finiteModule, finprod_eq_prod _ (finite_mulSupport_norm _)]
    refine Finset.prod_le_one (fun _ _ ↦ norm_nonneg _) fun v _ ↦ ?_
    have h2 := hd _ hτ v
    have h3 : ((diagonal K u * τ : IdeleGroup K) : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K := by
      simpa [coe_diagonal, u] using h2
    exact (Valued.toNormedField.norm_le_one_iff).2
      ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 h3)
  rw [finiteModule_mul] at h1
  rw [← one_div, le_div_iff₀' hu]
  exact h1

theorem sep_adele {L : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {c : ℝ} (hc0 : 0 < c)
    (hc : ∀ τ : IdeleGroup K, (τ : 𝔸[K]).2 ∈ idealFiniteAdeles L → finiteModule τ ≤ c)
    (t : IdeleGroup K) {a a' : K} (ha : ((t : 𝔸[K]) * algebraMap K 𝔸[K] a).2 ∈ idealFiniteAdeles L)
    (ha' : ((t : 𝔸[K]) * algebraMap K 𝔸[K] a').2 ∈ idealFiniteAdeles L) (hne : a ≠ a') :
    (ideleModule K t : ℝ) / c ≤
      ‖homeomorphMixedSpace K ((t : 𝔸[K]) * algebraMap K 𝔸[K] a).1 -
        homeomorphMixedSpace K ((t : 𝔸[K]) * algebraMap K 𝔸[K] a').1‖ ^ Module.finrank ℚ K := by
  set u : Kˣ := Units.mk0 (a - a') (sub_ne_zero.2 hne)
  set τ : IdeleGroup K := t * diagonal K u
  have hτ : (τ : 𝔸[K]) = (t : 𝔸[K]) * algebraMap K 𝔸[K] a - (t : 𝔸[K]) * algebraMap K 𝔸[K] a' := by
    simp [τ, u, coe_diagonal, mul_sub, map_sub]
  have hmem : (τ : 𝔸[K]).2 ∈ idealFiniteAdeles L := by
    rw [hτ]
    exact sub_mem ha ha'
  have hmod : (ideleModule K τ : ℝ) = (ideleModule K t : ℝ) := by
    simp [τ, ideleModule_diagonal]
  set Z := ‖homeomorphMixedSpace K ((t : 𝔸[K]) * algebraMap K 𝔸[K] a).1 -
        homeomorphMixedSpace K ((t : 𝔸[K]) * algebraMap K 𝔸[K] a').1‖
  have hZ : ‖homeomorphMixedSpace K (τ : 𝔸[K]).1‖ = Z := by
    have : homeomorphMixedSpace K (τ : 𝔸[K]).1 =
        homeomorphMixedSpace K ((t : 𝔸[K]) * algebraMap K 𝔸[K] a).1 -
        homeomorphMixedSpace K ((t : 𝔸[K]) * algebraMap K 𝔸[K] a').1 := by
      rw [hτ]
      exact map_sub (Adele2.infRingHom (K := K)) _ _
    rw [this]
  have hinf : infiniteModule τ ≤ Z ^ Module.finrank ℚ K := by
    rw [infiniteModule, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun _ _ ↦ by positivity) fun w _ ↦ pow_le_pow_left₀ (norm_nonneg _) ?_ _
    rw [← hZ]
    exact norm_le_norm_homeomorphMixedSpace _ w
  rw [div_le_iff₀ hc0, ← hmod, ideleModule_apply]
  exact mul_le_mul hinf (hc τ hmem) (finiteModule_pos τ).le (by positivity)

theorem theta_bound (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {A : ℕ} (hA : Module.finrank ℚ K < A) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ t : IdeleGroup K,
      Summable (fun a : K ↦ adeleWeight L A ((t : 𝔸[K]) * algebraMap K 𝔸[K] a)) ∧
      ∑' a : K, adeleWeight L A ((t : 𝔸[K]) * algebraMap K 𝔸[K] a) ≤
        c * (1 + ((ideleModule K t : ℝ))⁻¹) := by
  have hfr : Module.finrank ℝ (mixedSpace K) = Module.finrank ℚ K := mixedEmbedding.finrank K
  have hd : 0 < Module.finrank ℚ K := Module.finrank_pos
  obtain ⟨P, hP, hpack⟩ := packing (E := mixedSpace K) (volume : Measure (mixedSpace K)) (A := A)
    (by rw [hfr]; exact hA) (by rw [hfr]; exact hd)
  obtain ⟨c₁, hc₁, hfin⟩ := exists_finiteModule_le L
  refine ⟨P * max 1 c₁, by positivity, fun t ↦ ?_⟩
  set s : ℝ := (ideleModule K t : ℝ)
  have hs : 0 < s := (ideleModule K t).2
  set f : K → ℝ := fun a ↦ adeleWeight L A ((t : 𝔸[K]) * algebraMap K 𝔸[K] a)
  set Y : K → mixedSpace K := fun a ↦ homeomorphMixedSpace K ((t : 𝔸[K]) * algebraMap K 𝔸[K] a).1
  have hf0 : ∀ a, 0 ≤ f a := fun a ↦ adeleWeight_nonneg _ _ _
  have hbound : ∀ F : Finset K, ∑ a ∈ F, f a ≤ P * max 1 c₁ * (1 + s⁻¹) := by
    intro F
    set F' := F.filter fun a ↦ ((t : 𝔸[K]) * algebraMap K 𝔸[K] a).2 ∈ idealFiniteAdeles L
    have hF' : ∀ a ∈ F', ((t : 𝔸[K]) * algebraMap K 𝔸[K] a).2 ∈ idealFiniteAdeles L :=
      fun a ha ↦ (Finset.mem_filter.1 ha).2
    have hsep : ∀ a ∈ F', ∀ a' ∈ F', a ≠ a' → s / c₁ ≤ ‖Y a - Y a'‖ ^ Module.finrank ℚ K :=
      fun a ha a' ha' hne ↦ sep_adele hc₁ hfin t (hF' a ha) (hF' a' ha') hne
    have hη : 0 < s / c₁ := by positivity
    have hinj : Set.InjOn Y F' := by
      intro a ha a' ha' h
      by_contra hne
      have := hsep a ha a' ha' hne
      rw [h, sub_self, norm_zero, zero_pow hd.ne'] at this
      exact absurd this (not_le.2 hη)
    have h1 : ∑ a ∈ F, f a = ∑ y ∈ F'.image Y, ((1 + ‖y‖) ^ A)⁻¹ := by
      rw [Finset.sum_image hinj, Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      simp only [f, Y, adeleWeight]
    have h2 := hpack (s / c₁) hη (F'.image Y) (by
      intro y hy y' hy' hne
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hy'
      rw [hfr]
      exact hsep a ha a' ha' fun h ↦ hne (by rw [h]))
    rw [h1]
    refine h2.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hP
    have h3 : (s / c₁)⁻¹ = c₁ * s⁻¹ := by field_simp
    rw [h3]
    have h4 : 1 ≤ max 1 c₁ := le_max_left _ _
    have h5 : c₁ ≤ max 1 c₁ := le_max_right _ _
    have h6 : 0 ≤ s⁻¹ := by positivity
    nlinarith
  have hsum : Summable f := summable_of_sum_le hf0 hbound
  exact ⟨hsum, hsum.tsum_le_of_sum_le hbound⟩

theorem rpow_le_add {s a x b : ℝ} (hs : 0 < s) (hax : a ≤ x) (hxb : x ≤ b) :
    s ^ x ≤ s ^ a + s ^ b := by
  rcases le_or_gt 1 s with h | h
  · exact (Real.rpow_le_rpow_of_exponent_le h hxb).trans (le_add_of_nonneg_left (by positivity))
  · exact (Real.rpow_le_rpow_of_exponent_ge hs h.le hax).trans (le_add_of_nonneg_right (by positivity))

theorem one_add_inv_pow_mul_rpow_le {s : ℝ} (hs : 0 < s) (x : ℝ) (n : ℕ) :
    (1 + s⁻¹) ^ n * s ^ x ≤ 2 ^ n * (s ^ x + s ^ (x - n)) := by
  have hx : 0 < s ^ x := by positivity
  have hy : 0 < s ^ (x - n) := by positivity
  rcases le_or_gt 1 s with h | h
  · have h1 : 1 + s⁻¹ ≤ 2 := by
      have := inv_le_one_of_one_le₀ h
      linarith
    calc (1 + s⁻¹) ^ n * s ^ x ≤ 2 ^ n * s ^ x := by gcongr
      _ ≤ 2 ^ n * (s ^ x + s ^ (x - n)) := by gcongr; linarith
  · have h1 : 1 + s⁻¹ ≤ 2 * s⁻¹ := by
      have := (one_le_inv₀ hs).2 h.le
      linarith
    have h2 : s ^ (x - n) = (s⁻¹) ^ n * s ^ x := by
      rw [Real.rpow_sub hs, Real.rpow_natCast, inv_pow]
      field_simp
    calc (1 + s⁻¹) ^ n * s ^ x ≤ (2 * s⁻¹) ^ n * s ^ x := by gcongr
      _ = 2 ^ n * s ^ (x - n) := by rw [h2, mul_pow]; ring
      _ ≤ 2 ^ n * (s ^ x + s ^ (x - n)) := by gcongr; linarith

theorem sum_prod_le {f : K → ℝ} (hf : ∀ a, 0 ≤ f a) (hs : Summable f) {i : ι} (F : Finset (ι → K))
    (hF : ∀ ν ∈ F, ν i = 1) :
    ∑ ν ∈ F, ∏ j, f (ν j) ≤ f 1 * (∑' a, f a) ^ (Fintype.card ι - 1) := by
  set S : Finset K := F.biUnion fun ν ↦ Finset.univ.image ν
  set E := {j : ι // j ≠ i}
  set res : (ι → K) → E → K := fun ν j ↦ ν j
  have hinj : Set.InjOn res F := by
    intro ν hν μ hμ h
    funext j
    by_cases hj : j = i
    · rw [hj, hF ν hν, hF μ hμ]
    · exact congrFun h ⟨j, hj⟩
  have hsplit : ∀ ν ∈ F, ∏ j, f (ν j) = f 1 * ∏ j : E, f (res ν j) := by
    intro ν hν
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hF ν hν]
    congr 1
    refine (Finset.prod_subtype (Finset.univ.erase i) (fun j ↦ ?_) _)
    simp
  have hT : ∑ a ∈ S, f a ≤ ∑' a, f a := hs.sum_le_tsum _ fun a _ ↦ hf a
  have hS0 : 0 ≤ ∑ a ∈ S, f a := Finset.sum_nonneg fun a _ ↦ hf a
  calc ∑ ν ∈ F, ∏ j, f (ν j) = f 1 * ∑ ν ∈ F, ∏ j : E, f (res ν j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hsplit
    _ = f 1 * ∑ p ∈ F.image res, ∏ j : E, f (p j) := by
        rw [Finset.sum_image hinj]
    _ ≤ f 1 * ∑ p ∈ Fintype.piFinset fun _ : E ↦ S, ∏ j : E, f (p j) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ?_
          fun p _ _ ↦ Finset.prod_nonneg fun j _ ↦ hf _) (hf 1)
        intro p hp
        obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
        refine Fintype.mem_piFinset.2 fun j ↦ Finset.mem_biUnion.2 ⟨ν, hν, ?_⟩
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    _ = f 1 * (∑ a ∈ S, f a) ^ (Fintype.card ι - 1) := by
        rw [← Finset.prod_univ_sum, Finset.prod_const, Finset.card_univ]
        congr 2
        simp [E, Fintype.card_subtype_compl]
    _ ≤ f 1 * (∑' a, f a) ^ (Fintype.card ι - 1) := by gcongr; exact hf 1

def tw (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (t : IdeleGroup K) (a : K) : ℝ :=
  adeleWeight L A ((t : 𝔸[K]) * algebraMap K 𝔸[K] a)

theorem tw_nonneg (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (t : IdeleGroup K) (a : K) :
    0 ≤ tw L A t a := adeleWeight_nonneg _ _ _

theorem tw_le_one (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (t : IdeleGroup K) (a : K) :
    tw L A t a ≤ 1 := adeleWeight_le_one _ _ _

theorem continuous_tw (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (a : K) :
    Continuous fun t : IdeleGroup K ↦ tw L A t a :=
  (continuous_adeleWeight L A).comp (Units.continuous_val.mul continuous_const)

def lineFn (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (x : ℝ) (ν : ι → K) (t : IdeleGroup K) : ℝ :=
  (∏ j, tw L A t (ν j)) * (ideleModule K t : ℝ) ^ x

def lineInt (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (x : ℝ) (ν : ι → K) : ℝ :=
  ∫ t, lineFn L A x ν t ∂ideleMeasure K

theorem lineFn_nonneg (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (x : ℝ) (ν : ι → K) (t : IdeleGroup K) :
    0 ≤ lineFn L A x ν t :=
  mul_nonneg (Finset.prod_nonneg fun _ _ ↦ tw_nonneg _ _ _ _) (Real.rpow_nonneg (ideleModule K t).2.le _)

theorem lineInt_nonneg (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (x : ℝ) (ν : ι → K) :
    0 ≤ lineInt L A x ν := integral_nonneg fun t ↦ lineFn_nonneg L A x ν t

theorem continuous_lineFn (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) {x : ℝ} (hx : 0 ≤ x) (ν : ι → K) :
    Continuous (lineFn L A x ν) :=
  (continuous_finset_prod _ fun j _ ↦ continuous_tw L A (ν j)).mul
    (continuous_ideleModule_val.rpow_const fun _ ↦ Or.inr hx)

theorem lineFn_mul_diagonal (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (x : ℝ) (ν : ι → K) (c : Kˣ)
    (t : IdeleGroup K) :
    lineFn L A x ν (t * diagonal K c) = lineFn L A x (fun j ↦ (c : K) * ν j) t := by
  simp only [lineFn, tw, map_mul, Units.val_mul, coe_diagonal, ideleModule_diagonal, mul_one, mul_assoc]

theorem lineInt_smul (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (x : ℝ) (ν : ι → K) (c : Kˣ) :
    lineInt L A x (fun j ↦ (c : K) * ν j) = lineInt L A x ν := by
  simp only [lineInt, ← lineFn_mul_diagonal]
  exact integral_mul_right_eq_self (lineFn L A x ν) (diagonal K c)

theorem integrable_lineFn {L : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {A : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (hI : Integrable (fun t : IdeleGroup K ↦ adeleWeight L A (t : 𝔸[K]) * (ideleModule K t : ℝ) ^ x)
      (ideleMeasure K)) {ν : ι → K} {i : ι} (hν : ν i = 1) :
    Integrable (lineFn L A x ν) (ideleMeasure K) := by
  refine hI.mono' (continuous_lineFn L A hx ν).aestronglyMeasurable (Eventually.of_forall fun t ↦ ?_)
  rw [Real.norm_of_nonneg (lineFn_nonneg L A x ν t)]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (ideleModule K t).2.le _)
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hν]
  have h1 : tw L A t 1 = adeleWeight L A (t : 𝔸[K]) := by simp [tw]
  rw [h1]
  exact mul_le_of_le_one_right (adeleWeight_nonneg _ _ _)
    (Finset.prod_le_one (fun _ _ ↦ tw_nonneg _ _ _ _) fun _ _ ↦ tw_le_one _ _ _ _)

theorem summable_lineInt {L : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {A : ℕ} {x c : ℝ} (hx : 1 < x) (hc : 0 ≤ c)
    (hI₁ : Integrable (fun t : IdeleGroup K ↦ adeleWeight L A (t : 𝔸[K]) * (ideleModule K t : ℝ) ^ x)
      (ideleMeasure K))
    (hI₂ : Integrable (fun t : IdeleGroup K ↦ adeleWeight L A (t : 𝔸[K]) *
      (ideleModule K t : ℝ) ^ (x - ((Fintype.card ι - 1 : ℕ) : ℝ))) (ideleMeasure K))
    (hθ : ∀ t : IdeleGroup K, Summable (fun a : K ↦ tw L A t a) ∧
      ∑' a : K, tw L A t a ≤ c * (1 + ((ideleModule K t : ℝ))⁻¹)) (i : ι) :
    Summable fun ν : ι → K ↦ if ν i = 1 then lineInt L A x ν else 0 := by
  set n := Fintype.card ι - 1
  set B : IdeleGroup K → ℝ := fun t ↦ c ^ n * 2 ^ n *
    (adeleWeight L A (t : 𝔸[K]) * (ideleModule K t : ℝ) ^ x +
      adeleWeight L A (t : 𝔸[K]) * (ideleModule K t : ℝ) ^ (x - (n : ℝ)))
  have hB : Integrable B (ideleMeasure K) := (hI₁.add hI₂).const_mul _
  refine summable_of_sum_le (c := ∫ t, B t ∂ideleMeasure K)
    (fun ν ↦ by split_ifs; exacts [lineInt_nonneg _ _ _ _, le_rfl]) fun F ↦ ?_
  rw [← Finset.sum_filter]
  set F' := F.filter fun ν ↦ ν i = 1
  have hF' : ∀ ν ∈ F', ν i = 1 := fun ν hν ↦ (Finset.mem_filter.1 hν).2
  have hint : ∀ ν ∈ F', Integrable (lineFn L A x ν) (ideleMeasure K) := fun ν hν ↦
    integrable_lineFn (by linarith) hI₁ (hF' ν hν)
  simp only [lineInt]
  rw [← integral_finset_sum _ hint]
  refine integral_mono (integrable_finset_sum _ hint) hB fun t ↦ ?_
  obtain ⟨hs, ht⟩ := hθ t
  set s : ℝ := (ideleModule K t : ℝ)
  have hs0 : 0 < s := (ideleModule K t).2
  have h1 : tw L A t 1 = adeleWeight L A (t : 𝔸[K]) := by simp [tw]
  have hw0 := adeleWeight_nonneg L A (t : 𝔸[K])
  have h2 := sum_prod_le (fun a ↦ tw_nonneg L A t a) hs F' hF'
  rw [h1] at h2
  have hsx : 0 ≤ s ^ x := by positivity
  have hT0 : 0 ≤ ∑' a : K, tw L A t a := tsum_nonneg fun a ↦ tw_nonneg L A t a
  calc ∑ ν ∈ F', lineFn L A x ν t = (∑ ν ∈ F', ∏ j, tw L A t (ν j)) * s ^ x := by
        rw [Finset.sum_mul]; rfl
    _ ≤ (adeleWeight L A (t : 𝔸[K]) * (∑' a : K, tw L A t a) ^ n) * s ^ x := by gcongr
    _ ≤ (adeleWeight L A (t : 𝔸[K]) * (c * (1 + s⁻¹)) ^ n) * s ^ x := by gcongr
    _ = c ^ n * adeleWeight L A (t : 𝔸[K]) * ((1 + s⁻¹) ^ n * s ^ x) := by rw [mul_pow]; ring
    _ ≤ c ^ n * adeleWeight L A (t : 𝔸[K]) * (2 ^ n * (s ^ x + s ^ (x - n))) :=
        mul_le_mul_of_nonneg_left (one_add_inv_pow_mul_rpow_le hs0 x n) (mul_nonneg (pow_nonneg hc n) hw0)
    _ = B t := by simp only [B]; ring

theorem clause_one {Ψ : (ι → 𝔸[K]) → ℂ} (hΨ : Ψ ∈ GJMatrix.schwartzBruhatPi K ι) (i₀ : ι) (a b : ℝ)
    (C : Set (GL ι 𝔸[K])) (ha : 1 < a) (hC : IsCompact C) :
    ∃ f : IdeleGroup K → ℝ, Integrable f (ideleMeasure K) ∧ ∀ x : ℝ, a ≤ x → x ≤ b → ∀ m ∈ C,
      ∀ t : IdeleGroup K,
        ‖Ψ ((t : 𝔸[K]) • ((m : Matrix ι ι 𝔸[K]) *ᵥ Pi.single i₀ 1))‖ *
          (ideleModule K t : ℝ) ^ x ≤ f t := by
  by_cases hab : a ≤ b
  · obtain ⟨A₁, h₁⟩ := integrable_weight (K := K) ha
    obtain ⟨A₂, h₂⟩ := integrable_weight (K := K) (ha.trans_le hab)
    set A := max A₁ A₂
    obtain ⟨M, L, hM, hb⟩ := exists_majorant hΨ hC A
    refine ⟨fun t ↦ M * (adeleWeight L A (t : 𝔸[K]) * (ideleModule K t : ℝ) ^ a +
      adeleWeight L A (t : 𝔸[K]) * (ideleModule K t : ℝ) ^ b),
      ((h₁ L A (le_max_left _ _)).add (h₂ L A (le_max_right _ _))).const_mul M, ?_⟩
    intro x hax hxb m hm t
    have hs0 : 0 < (ideleModule K t : ℝ) := (ideleModule K t).2
    have hsm : (t : 𝔸[K]) • ((m : Matrix ι ι 𝔸[K]) *ᵥ Pi.single i₀ 1) =
        (m : Matrix ι ι 𝔸[K]) *ᵥ ((t : 𝔸[K]) • Pi.single i₀ 1) := (Matrix.mulVec_smul _ _ _).symm
    have hprod : ∏ i, adeleWeight L A (((t : 𝔸[K]) • (Pi.single i₀ 1 : ι → 𝔸[K])) i) =
        adeleWeight L A (t : 𝔸[K]) := by
      rw [Fintype.prod_eq_single i₀ fun i hi ↦ by simp [Pi.single_eq_of_ne hi]]
      simp
    have h3 := hb m hm ((t : 𝔸[K]) • Pi.single i₀ 1)
    rw [hprod, ← hsm] at h3
    have hw0 := adeleWeight_nonneg L A (t : 𝔸[K])
    calc _ ≤ (M * adeleWeight L A (t : 𝔸[K])) * (ideleModule K t : ℝ) ^ x := by gcongr
      _ ≤ (M * adeleWeight L A (t : 𝔸[K])) * ((ideleModule K t : ℝ) ^ a + (ideleModule K t : ℝ) ^ b) := by
          gcongr
          exact rpow_le_add hs0 hax hxb
      _ = _ := by ring
  · exact ⟨0, integrable_zero _ _ _, fun x hax hxb ↦ absurd (hax.trans hxb) hab⟩

theorem clause_two {Ψ : (ι → 𝔸[K]) → ℂ} (hΨ : Ψ ∈ GJMatrix.schwartzBruhatPi K ι) (x : ℝ)
    (C : Set (GL ι 𝔸[K])) (hx : max 1 (Fintype.card ι : ℝ) < x) (hC : IsCompact C) :
    ∃ u : Projectivization K (ι → K) → ℝ, Summable u ∧ ∀ m ∈ C, ∀ l,
      ∫ t : IdeleGroup K, ‖Ψ ((t : 𝔸[K]) • ((m : Matrix ι ι 𝔸[K]) *ᵥ ratV l.rep))‖ *
        (ideleModule K t : ℝ) ^ x ∂ideleMeasure K ≤ u l := by
  have hx1 : 1 < x := (le_max_left _ _).trans_lt hx
  have hxN : (Fintype.card ι : ℝ) < x := (le_max_right _ _).trans_lt hx
  set n := Fintype.card ι - 1
  have hx2 : 1 < x - (n : ℝ) := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
    · have : n = 0 := by simp [n, h0]
      simpa [this] using hx1
    · have : (n : ℝ) = (Fintype.card ι : ℝ) - 1 := by
        simp only [n]
        rw [Nat.cast_sub h0]
        simp
      rw [this]
      linarith
  obtain ⟨A₁, h₁⟩ := integrable_weight (K := K) hx1
  obtain ⟨A₂, h₂⟩ := integrable_weight (K := K) hx2
  set A := max (max A₁ A₂) (Module.finrank ℚ K + 1)
  have hA₁ : A₁ ≤ A := (le_max_left _ _).trans (le_max_left _ _)
  have hA₂ : A₂ ≤ A := (le_max_right _ _).trans (le_max_left _ _)
  have hAd : Module.finrank ℚ K < A := Nat.lt_of_succ_le (le_max_right _ _)
  obtain ⟨M, L, hM, hb⟩ := exists_majorant hΨ hC A
  obtain ⟨c, hc, hθ⟩ := theta_bound L hAd
  have hsum := summable_lineInt (ι := ι) hx1 hc (h₁ L A hA₁) (h₂ L A hA₂) hθ
  have hex : ∀ l : Projectivization K (ι → K), ∃ i, l.rep i ≠ 0 := fun l ↦ by
    by_contra h
    push_neg at h
    exact l.rep_nonzero (funext h)
  choose ix hix using hex
  set ν : Projectivization K (ι → K) → ι → K := fun l j ↦ (l.rep (ix l))⁻¹ * l.rep j
  have hν1 : ∀ l, ν l (ix l) = 1 := fun l ↦ inv_mul_cancel₀ (hix l)
  have hinj : Function.Injective ν := by
    intro l l' h
    rw [← l.mk_rep, ← l'.mk_rep, Projectivization.mk_eq_mk_iff']
    refine ⟨(l.rep (ix l)) * (l'.rep (ix l'))⁻¹, funext fun j ↦ ?_⟩
    have := congrFun h j
    simp only [ν] at this
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_assoc, ← this, ← mul_assoc, mul_inv_cancel₀ (hix l), one_mul]
  refine ⟨fun l ↦ M * ∑ i, if ν l i = 1 then lineInt L A x (ν l) else 0,
    (summable_sum fun i _ ↦ (hsum i).comp_injective hinj).mul_left M, ?_⟩
  intro m hm l
  have hlin : lineInt L A x (ν l) = lineInt L A x l.rep :=
    lineInt_smul L A x l.rep (Units.mk0 _ (inv_ne_zero (hix l)))
  have hle : lineInt L A x (ν l) ≤ ∑ i, if ν l i = 1 then lineInt L A x (ν l) else 0 := by
    have := Finset.single_le_sum (f := fun i ↦ if ν l i = 1 then lineInt L A x (ν l) else 0)
      (fun i _ ↦ by split_ifs; exacts [lineInt_nonneg _ _ _ _, le_rfl]) (Finset.mem_univ (ix l))
    simpa only [hν1, if_true] using this
  have hintν : Integrable (lineFn L A x (ν l)) (ideleMeasure K) :=
    integrable_lineFn (by linarith) (h₁ L A hA₁) (hν1 l)
  have hintr : Integrable (lineFn L A x l.rep) (ideleMeasure K) := by
    have h := hintν.comp_mul_right (diagonal K (Units.mk0 _ (hix l)))
    refine h.congr (Eventually.of_forall fun t ↦ ?_)
    simp only [lineFn_mul_diagonal]
    congr 1
    funext j
    simp only [ν, Units.val_mk0]
    rw [← mul_assoc, mul_inv_cancel₀ (hix l), one_mul]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hle hM)
  rw [hlin, lineInt, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun t ↦ by
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (ideleModule K t).2.le _)) (hintr.const_mul M)
    (Eventually.of_forall fun t ↦ ?_)
  have hsm : (t : 𝔸[K]) • ((m : Matrix ι ι 𝔸[K]) *ᵥ ratV l.rep) =
      (m : Matrix ι ι 𝔸[K]) *ᵥ ((t : 𝔸[K]) • ratV l.rep) := (Matrix.mulVec_smul _ _ _).symm
  have h3 := hb m hm ((t : 𝔸[K]) • ratV l.rep)
  rw [← hsm] at h3
  have hs0 : 0 ≤ (ideleModule K t : ℝ) ^ x := Real.rpow_nonneg (ideleModule K t).2.le _
  calc _ ≤ (M * ∏ i, adeleWeight L A (((t : 𝔸[K]) • ratV l.rep) i)) * (ideleModule K t : ℝ) ^ x :=
        mul_le_mul_of_nonneg_right h3 hs0
    _ = M * lineFn L A x l.rep t := by
        simp only [lineFn, tw, mul_assoc]
        rfl

theorem epConv : EpConv := fun _ _ _ _ _ _ _ hΨ ↦
  ⟨fun i₀ a b C ha hC ↦ clause_one hΨ i₀ a b C ha hC, fun x C hx hC ↦ clause_two hΨ x C hx hC⟩

end

end GlobalTheory.CompanionTheory.EpConvB
