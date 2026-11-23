import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.EvAdm

noncomputable section

namespace GlobalTheory.EvAdm

theorem norm_natCast_lt_one_of_dvd (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (c : ℕ) (hc : Ideal.absNorm v.asIdeal ∣ c) :
    ‖(c : v.adicCompletion F)‖ < 1 := by
  have hmem : (c : 𝓞 F) ∈ v.asIdeal := by
    obtain ⟨k, hk⟩ := hc
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hval := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (c : 𝓞 F)).2 hmem
  rw [Valued.toNormedField.norm_lt_one_iff]
  have e : (c : v.adicCompletion F) = (((algebraMap (𝓞 F) F (c : 𝓞 F)) : F) : v.adicCompletion F) := by
    rw [map_natCast]
    rw [show (((c : F)) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (c : F) from rfl,
      map_natCast]
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hval

theorem exists_nat_scaled_subset (F : Type) [Field F] [NumberField F]
    (U : Set (FiniteAdeleRing (𝓞 F) F)) (hU : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ m : ℕ, m ≠ 0 → N ∣ m → ∀ x : FiniteAdeleRing (𝓞 F) F,
      (∀ v : HeightOneSpectrum (𝓞 F),
        (algebraMap F (v.adicCompletion F) (m : F))⁻¹ * x v ∈ v.adicCompletionIntegers F) → x ∈ U := by
  classical
  have hAopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun _ => Valued.isOpen_valuationSubring _
  have hU' : U ∈ Filter.map (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)
      (𝓝 (fun v => ⟨0, zero_mem (v.adicCompletionIntegers F)⟩)) := by
    rw [← RestrictedProduct.nhds_eq_map_structureMap hAopen]
    exact hU
  have hU2 : (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite) ⁻¹'
      (U : Set (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)) ∈
      𝓝 (fun v : HeightOneSpectrum (𝓞 F) => (⟨0, zero_mem (v.adicCompletionIntegers F)⟩ :
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)))) := hU'
  rw [nhds_pi, Filter.mem_pi] at hU2
  obtain ⟨I, hI, t, ht, hIt⟩ := hU2
  have hε : ∀ v : HeightOneSpectrum (𝓞 F), ∃ ε > (0 : ℝ),
      ∀ y : (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
        ‖(y : v.adicCompletion F)‖ < ε → y ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hu
    refine ⟨ε, hε, fun y hy => hut (hball ?_)⟩
    simpa [Metric.mem_ball, dist_zero_right] using hy
  choose ε hεpos hεt using hε
  set c : ℕ := ∏ v ∈ hI.toFinset, Ideal.absNorm v.asIdeal with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Finset.prod_ne_zero_iff]
    intro v _
    exact (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hcv : ∀ v ∈ I, ‖(c : v.adicCompletion F)‖ < 1 := fun v hv =>
    norm_natCast_lt_one_of_dvd F v c (Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hv))
  have hev : ∀ v ∈ I, ∀ᶠ k in atTop, ‖(c : v.adicCompletion F)‖ ^ k < ε v := fun v hv =>
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hcv v hv)).eventually
      (Iio_mem_nhds (hεpos v))
  obtain ⟨k, hk⟩ := ((Filter.eventually_all_finite hI).2 hev).exists
  refine ⟨c ^ k, pow_ne_zero _ hc0, fun m hm hdvd x hx => ?_⟩
  obtain ⟨d, hd⟩ := hdvd
  have hmv : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) (m : F) = (m : v.adicCompletion F) :=
    fun v => map_natCast _ m
  have hm0 : ∀ v : HeightOneSpectrum (𝓞 F), (m : v.adicCompletion F) ≠ 0 :=
    fun v => by rw [← hmv]; exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hm)
  have hxv : ∀ v : HeightOneSpectrum (𝓞 F),
      x v = (m : v.adicCompletion F) * ((m : v.adicCompletion F)⁻¹ * x v) := by
    intro v
    rw [← mul_assoc, mul_inv_cancel₀ (hm0 v), one_mul]
  have hmem : ∀ v : HeightOneSpectrum (𝓞 F), x v ∈
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    intro v
    have h1 := hx v
    rw [hmv] at h1
    rw [hxv v]
    exact mul_mem (natCast_mem _ _) h1
  have hxe : x = RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
      (fun v => ⟨_, hmem v⟩) := by
    ext v
    rfl
  rw [hxe]
  apply hIt
  intro v hv
  apply hεt
  show ‖x v‖ < ε v
  have h1 := hx v
  rw [hmv] at h1
  have hz1 : ‖(m : v.adicCompletion F)⁻¹ * x v‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1
  have hd1 : ‖(d : v.adicCompletion F)‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (natCast_mem _ _)
  have hnm : ‖(m : v.adicCompletion F)‖ ≤ ‖(c : v.adicCompletion F)‖ ^ k := by
    rw [hd, Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow]
    calc ‖(c : v.adicCompletion F)‖ ^ k * ‖(d : v.adicCompletion F)‖
        ≤ ‖(c : v.adicCompletion F)‖ ^ k * 1 := by gcongr
      _ = _ := mul_one _
  rw [hxv v, norm_mul]
  calc ‖(m : v.adicCompletion F)‖ * ‖(m : v.adicCompletion F)⁻¹ * x v‖
      ≤ ‖(c : v.adicCompletion F)‖ ^ k * 1 := by gcongr
    _ < ε v := by rw [mul_one]; exact hk v hv

end GlobalTheory.EvAdm

namespace GlobalTheory.EvAdm

theorem exists_scaledInt_subset_of_mem_nhds : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (W : Set (κ → FiniteAdeleRing (𝓞 F) F)),
    W ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) → ∃ a : F, a ≠ 0 ∧
      (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ W := by
  intro F _ _ κ _ W hW
  classical
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, _, t, ht, hIt⟩ := hW
  have ht' : ∀ i, t i ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := fun i => ht i
  choose N hN0 hN using fun i => exists_nat_scaled_subset F (t i) (ht' i)
  have hP : (∏ i, N i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hN0 i
  refine ⟨((∏ i, N i : ℕ) : F), Nat.cast_ne_zero.2 hP, fun z hz => hIt ?_⟩
  intro i _
  exact hN i _ hP (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) (z i) (fun v => hz i v)

end GlobalTheory.EvAdm
