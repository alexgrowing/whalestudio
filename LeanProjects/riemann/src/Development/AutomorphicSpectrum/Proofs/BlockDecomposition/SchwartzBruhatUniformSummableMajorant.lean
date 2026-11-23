import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.RankOneEisenstein.Theta2Integral
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.EisRk1Bound

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem vecMul_vecMul_inv (x : Fin 2 → 𝔸[K]) (h : GL (Fin 2) 𝔸[K]) :
    (x ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[K])) ᵥ*
      ((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) = x := by
  rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

theorem continuous_infRingHom : Continuous (infRingHom (K := K)) := by
  exact (GroundTheory.Global.homeomorphMixedSpace K).continuous.comp continuous_fst

theorem continuous_finRingHom : Continuous (finRingHom (K := K)) := by
  exact continuous_snd

theorem continuous_inv_entry (i j : Fin 2) :
    Continuous fun h : GL (Fin 2) 𝔸[K] ↦
      ((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) i j := by
  exact Units.continuous_coe_inv.matrix_elem i j

theorem norm_vecMul_le (u : Fin 2 → mixedSpace K) (M : Matrix (Fin 2) (Fin 2) (mixedSpace K)) :
    ‖u ᵥ* M‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  simp only [Matrix.vecMul, dotProduct]
  calc ‖∑ i, u i * M i j‖ ≤ ∑ i, ‖u i * M i j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖u‖ * ‖M i j‖ := Finset.sum_le_sum fun i _ =>
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_le_pi_norm u i) (norm_nonneg _))
    _ = ‖u‖ * ∑ i, ‖M i j‖ := by rw [Finset.mul_sum]
    _ ≤ ‖u‖ * ∑ i, ∑ j', ‖M i j'‖ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => Finset.single_le_sum (f := fun j' => ‖M i j'‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ j)) (norm_nonneg _)
    _ = (∑ i, ∑ j', ‖M i j'‖) * ‖u‖ := mul_comm _ _

private theorem mul_mem_idealFiniteAdeles_of_mem_integral {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x a : 𝔸ᶠ[K]}
    (hx : x ∈ idealFiniteAdeles I) (ha : a ∈ integralFiniteAdeles (𝓞 K) K) :
    a * x ∈ idealFiniteAdeles I := by
  change ∀ v, Valued.v ((a * x) v) ≤ _
  intro v
  have h1 : Valued.v (x v) ≤ WithZero.exp (-FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) :=
    hx v
  have h2 : Valued.v (a v) ≤ 1 := (mem_adicCompletionIntegers _ _ _).mp (ha v)
  have h3 : (a * x) v = a v * x v := rfl
  rw [h3, Valuation.map_mul]
  calc Valued.v (a v) * Valued.v (x v) ≤ 1 * Valued.v (x v) := mul_le_mul' h2 le_rfl
    _ ≤ _ := by rw [one_mul]; exact h1

private theorem mem_idealFiniteAdeles_one_of_mem_integral {a : 𝔸ᶠ[K]} (ha : a ∈ integralFiniteAdeles (𝓞 K) K) :
    a ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
  change ∀ v, Valued.v (a v) ≤ _
  intro v
  rw [Units.val_one, FractionalIdeal.count_one, neg_zero, WithZero.exp_zero]
  exact (mem_adicCompletionIntegers _ _ _).mp (ha v)

theorem exists_fractionalIdeal_of_isCompact (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : Fin 2 → 𝔸ᶠ[K])
    {C : Set (GL (Fin 2) 𝔸[K])} (hC : IsCompact C) :
    ∃ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∀ h ∈ C, ∀ ξ : Fin 2 → K,
      (∀ i, finPart ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[K])) i - b i ∈
        idealFiniteAdeles I) → ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
  set S : Set 𝔸ᶠ[K] := ((⋃ i : Fin 2, ⋃ j : Fin 2,
      (fun h : GL (Fin 2) 𝔸[K] =>
        finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) i j)) '' C) ∪
      Set.range b) ∪ {1} with hS
  have hSc : IsCompact S :=
    ((isCompact_iUnion fun i => isCompact_iUnion fun j =>
      hC.image (continuous_finRingHom.comp (continuous_inv_entry i j))).union
      (isCompact_range continuous_of_discreteTopology)).union isCompact_singleton
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hSc
  have hL0 : ((I : FractionalIdeal (𝓞 K)⁰ K) ⊔ 1) ≠ 0 := by
    intro h0
    have h1 : (1 : FractionalIdeal (𝓞 K)⁰ K) ≤ 0 := h0 ▸ le_sup_right
    exact one_ne_zero (le_antisymm h1 (FractionalIdeal.zero_le _))
  set L : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 _ hL0 with hLdef
  have hIL : (idealFiniteAdeles I : Set 𝔸ᶠ[K]) ⊆ idealFiniteAdeles L :=
    idealFiniteAdeles_subset (by rw [hLdef, Units.val_mk0]; exact le_sup_left)
  have h1L : (idealFiniteAdeles (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Set 𝔸ᶠ[K]) ⊆ idealFiniteAdeles L :=
    idealFiniteAdeles_subset (by rw [hLdef, Units.val_mk0, Units.val_one]; exact le_sup_right)
  set e : K := algebraMap (𝓞 K) K d with he_def
  have he : e ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  have hE0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (e⁻¹ * e⁻¹) * (L : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    mul_ne_zero ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr
      (mul_ne_zero (inv_ne_zero he) (inv_ne_zero he))) (Units.ne_zero L)
  refine ⟨Units.mk0 _ hE0, fun h hh ξ hξ i => ?_⟩
  set y := finPart ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[K])) with hy
  have hrec : (fun i => algebraMap K 𝔸ᶠ[K] (ξ i)) =
      y ᵥ* ((((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K])).map finRingHom) := by
    rw [hy, ← finPart_vecMul, vecMul_vecMul_inv, finPart_algebraMap]
  have hξi : algebraMap K 𝔸ᶠ[K] (ξ i) = ∑ j, y j *
      finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) j i) := by
    rw [congrFun hrec i]
    rfl
  set E : 𝔸ᶠ[K] := algebraMap K 𝔸ᶠ[K] e with hEdef
  have hE1 : E ∈ integralFiniteAdeles (𝓞 K) K := by
    have := hd 1 (Or.inr rfl)
    rwa [mul_one] at this
  have hEs : ∀ j, E * finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) j i) ∈
      integralFiniteAdeles (𝓞 K) K := fun j =>
    hd _ (Or.inl (Or.inl (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨i, ⟨h, hh, rfl⟩⟩⟩)))
  have hEb : ∀ j, E * b j ∈ integralFiniteAdeles (𝓞 K) K := fun j =>
    hd _ (Or.inl (Or.inr ⟨j, rfl⟩))
  have hmemL : algebraMap K 𝔸ᶠ[K] (e * e * ξ i) ∈ idealFiniteAdeles L := by
    rw [map_mul, map_mul, hξi, Finset.mul_sum]
    refine sum_mem fun j _ => ?_
    have hsplit : E * E * (y j * finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) :
        Matrix (Fin 2) (Fin 2) 𝔸[K]) j i)) =
        (E * (E * finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) j i))) *
          (y j - b j) +
        (E * b j) * (E * finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) j i)) := by
      ring
    rw [hsplit]
    refine add_mem (hIL (mul_mem_idealFiniteAdeles_of_mem_integral (hξ j) (mul_mem hE1 (hEs j)))) ?_
    exact h1L (mem_idealFiniteAdeles_one_of_mem_integral (mul_mem (hEb j) (hEs j)))
  have hmem : e * e * ξ i ∈ (L : FractionalIdeal (𝓞 K)⁰ K) :=
    (algebraMap_mem_idealFiniteAdeles_iff L _).mp hmemL
  rw [Units.val_mk0]
  have hξeq : ξ i = (e⁻¹ * e⁻¹) * (e * e * ξ i) := by field_simp
  rw [hξeq]
  exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hmem

def latticeWeight (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (k : ℕ) (x : K) : ℝ :=
  if x ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then ((1 + ‖mixedEmbedding K x‖) ^ k)⁻¹ else 0

theorem latticeWeight_nonneg (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (k : ℕ) (x : K) :
    0 ≤ latticeWeight J k x := by
  unfold latticeWeight
  split_ifs <;> positivity

theorem summable_latticeWeight_mul (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Summable fun ξ : Fin 2 → K ↦
      latticeWeight J (Module.finrank ℤ (idealLattice K J) + 1) (ξ 0) *
        latticeWeight J (Module.finrank ℤ (idealLattice K J) + 1) (ξ 1) := by
  have hs : Summable (latticeWeight J (Module.finrank ℤ (idealLattice K J) + 1)) := by
    have := summable_ite_mem_of_summable_idealLattice J
      (h := fun z => ((1 + ‖z‖) ^ (Module.finrank ℤ (idealLattice K J) + 1))⁻¹)
      (summable_inv_one_add_norm_pow_idealLattice J)
    unfold latticeWeight
    exact this
  have h2 := Summable.mul_of_nonneg hs hs (fun x => latticeWeight_nonneg J _ x)
    (fun x => latticeWeight_nonneg J _ x)
  exact (finTwoArrowEquiv K).summable_iff.mpr h2

theorem exists_summable_bound_tensor_cosetIndicator2 (φ : 𝓢(Fin 2 → mixedSpace K, ℂ))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : Fin 2 → 𝔸ᶠ[K]) {C : Set (GL (Fin 2) 𝔸[K])}
    (hC : IsCompact C) :
    ∃ u : (Fin 2 → K) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : Fin 2 → K,
      ‖schwartzBruhatTensor2 φ (finiteTensor2 fun i ↦ cosetIndicator I (b i))
        ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[K]))‖ ≤ u ξ := by
  obtain ⟨J, hJ⟩ := exists_fractionalIdeal_of_isCompact I b hC
  set N := Module.finrank ℤ (idealLattice K J) + 1 with hN
  have hcont : Continuous fun h : GL (Fin 2) 𝔸[K] => ∑ i, ∑ j,
      ‖infRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) i j)‖ :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_infRingHom.comp (continuous_inv_entry i j)).norm
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  set A : ℝ := 2 ^ (2 * N) *
    (Finset.Iic (2 * N, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) φ with hAdef
  have hA : ∀ w, (1 + ‖w‖) ^ (2 * N) * ‖φ w‖ ≤ A := fun w => by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (2 * N, 0)) le_rfl le_rfl φ w
    rwa [norm_iteratedFDeriv_zero] at this
  have hA0 : 0 ≤ A := le_trans (by positivity) (hA 0)
  set M' : ℝ := max 1 M with hM'
  have hM'1 : 1 ≤ M' := le_max_left _ _
  refine ⟨fun ξ => A * M' ^ (2 * N) * (latticeWeight J N (ξ 0) * latticeWeight J N (ξ 1)),
    (summable_latticeWeight_mul J).mul_left _, ?_⟩
  intro h hh ξ
  have hl0 := latticeWeight_nonneg J N (ξ 0)
  have hl1 := latticeWeight_nonneg J N (ξ 1)
  have hu0 : 0 ≤ A * M' ^ (2 * N) * (latticeWeight J N (ξ 0) * latticeWeight J N (ξ 1)) := by
    positivity
  set x := (fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[K]) with hx
  show ‖φ (infPart x) * finiteTensor2 (fun i ↦ cosetIndicator I (b i)) (finPart x)‖ ≤ _
  by_cases hmem : ∀ i, finPart x i - b i ∈ idealFiniteAdeles I
  · have hJξ := hJ h hh ξ hmem
    have hind : ‖finiteTensor2 (fun i ↦ cosetIndicator I (b i)) (finPart x)‖ ≤ 1 := by
      simp only [finiteTensor2, norm_prod]
      refine Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => ?_)
      simp only [cosetIndicator]
      refine (norm_indicator_le_norm_self _ _).trans ?_
      simp
    have hinv : emb2 K ξ = infPart x ᵥ*
        ((((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K])).map infRingHom) := by
      rw [hx, ← infPart_vecMul, vecMul_vecMul_inv, infPart_algebraMap]
    have hE : ‖emb2 K ξ‖ ≤ M * ‖infPart x‖ := by
      rw [hinv]
      refine (norm_vecMul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      simp only [Matrix.map_apply]
      exact (Real.le_norm_self _).trans (hM h hh)
    have hE' : ‖emb2 K ξ‖ ≤ M' * ‖infPart x‖ :=
      hE.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    have hcomp : ∀ i, 1 + ‖mixedEmbedding K (ξ i)‖ ≤ M' * (1 + ‖infPart x‖) := fun i => by
      have h1 : ‖mixedEmbedding K (ξ i)‖ ≤ ‖emb2 K ξ‖ := norm_le_pi_norm (emb2 K ξ) i
      nlinarith [norm_nonneg (infPart x)]
    have hP : (1 + ‖mixedEmbedding K (ξ 0)‖) ^ N * (1 + ‖mixedEmbedding K (ξ 1)‖) ^ N ≤
        M' ^ (2 * N) * (1 + ‖infPart x‖) ^ (2 * N) := by
      calc (1 + ‖mixedEmbedding K (ξ 0)‖) ^ N * (1 + ‖mixedEmbedding K (ξ 1)‖) ^ N
          ≤ (M' * (1 + ‖infPart x‖)) ^ N * (M' * (1 + ‖infPart x‖)) ^ N := by
            gcongr
            · exact hcomp 0
            · exact hcomp 1
        _ = M' ^ (2 * N) * (1 + ‖infPart x‖) ^ (2 * N) := by
          rw [← pow_add, ← two_mul, mul_pow]
    have hφ := hA (infPart x)
    beta_reduce
    unfold latticeWeight
    rw [if_pos (hJξ 0), if_pos (hJξ 1), norm_mul]
    have hpos0 : 0 < (1 + ‖mixedEmbedding K (ξ 0)‖) ^ N := by positivity
    have hpos1 : 0 < (1 + ‖mixedEmbedding K (ξ 1)‖) ^ N := by positivity
    calc ‖φ (infPart x)‖ * ‖finiteTensor2 (fun i ↦ cosetIndicator I (b i)) (finPart x)‖
        ≤ ‖φ (infPart x)‖ * 1 := mul_le_mul_of_nonneg_left hind (norm_nonneg _)
      _ = ‖φ (infPart x)‖ := mul_one _
      _ ≤ A * M' ^ (2 * N) * (((1 + ‖mixedEmbedding K (ξ 0)‖) ^ N)⁻¹ *
            ((1 + ‖mixedEmbedding K (ξ 1)‖) ^ N)⁻¹) := by
        rw [← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (mul_pos hpos0 hpos1)]
        calc ‖φ (infPart x)‖ * ((1 + ‖mixedEmbedding K (ξ 0)‖) ^ N *
              (1 + ‖mixedEmbedding K (ξ 1)‖) ^ N)
            ≤ ‖φ (infPart x)‖ * (M' ^ (2 * N) * (1 + ‖infPart x‖) ^ (2 * N)) :=
              mul_le_mul_of_nonneg_left hP (norm_nonneg _)
          _ = M' ^ (2 * N) * ((1 + ‖infPart x‖) ^ (2 * N) * ‖φ (infPart x)‖) := by ring
          _ ≤ M' ^ (2 * N) * A := mul_le_mul_of_nonneg_left hφ (by positivity)
          _ = A * M' ^ (2 * N) := mul_comm _ _
  · push Not at hmem
    obtain ⟨i, hi⟩ := hmem
    have h0 : finiteTensor2 (fun i ↦ cosetIndicator I (b i)) (finPart x) = 0 := by
      simp only [finiteTensor2]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [cosetIndicator]
      apply Set.indicator_of_notMem
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
      exact hi
    rw [h0, mul_zero, norm_zero]
    exact hu0

theorem exists_summable_bound_theta2 {F : (Fin 2 → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhat2 K)
    {C : Set (GL (Fin 2) 𝔸[K])} (hC : IsCompact C) :
    ∃ u : (Fin 2 → K) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : Fin 2 → K,
      ‖F ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[K]))‖ ≤ u ξ := by
  rw [schwartzBruhat2_eq_cosetSpan2] at hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ, I, b, rfl⟩ := hF
    exact exists_summable_bound_tensor_cosetIndicator2 φ I b hC
  | zero => exact ⟨0, summable_zero, fun h _ ξ => by simp⟩
  | add F G _ _ hF hG =>
    obtain ⟨u, hu, hFu⟩ := hF
    obtain ⟨v, hv, hGv⟩ := hG
    exact ⟨u + v, hu.add hv, fun h hh ξ =>
      (norm_add_le _ _).trans (add_le_add (hFu h hh ξ) (hGv h hh ξ))⟩
  | smul c F _ hF =>
    obtain ⟨u, hu, hFu⟩ := hF
    exact ⟨fun ξ => ‖c‖ * u ξ, hu.mul_left _, fun h hh ξ => by
      rw [Pi.smul_apply, smul_eq_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hFu h hh ξ) (norm_nonneg _)⟩

end

end GlobalTheory.CompanionTheory.EisRk1Bound
