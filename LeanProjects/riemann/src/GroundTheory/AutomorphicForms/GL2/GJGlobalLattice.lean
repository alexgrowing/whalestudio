import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalDefs
import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDecay

open MeasureTheory NumberField Topology Filter Set
open scoped NumberField.AdeleRing Classical nonZeroDivisors

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open GroundTheory.Global GJMatrix

variable {K : Type*} [Field K] [NumberField K]

theorem norm_apply_le_norm_homeomorphMixedSpace (x : InfiniteAdeleRing K) (w : InfinitePlace K) :
    ‖x w‖ ≤ ‖homeomorphMixedSpace K x‖ := by
  rw [homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  by_cases hw : w.IsReal
  · refine le_trans ?_ (norm_fst_le _)
    refine le_trans ?_ (norm_le_pi_norm _ ⟨w, hw⟩)
    simp [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero]
  · refine le_trans ?_ (norm_snd_le _)
    refine le_trans ?_ (norm_le_pi_norm _ ⟨w, InfinitePlace.not_isReal_iff_isComplex.1 hw⟩)
    simp [(InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero]

theorem norm_homeomorphMixedSpace_le_sum (x : InfiniteAdeleRing K) :
    ‖homeomorphMixedSpace K x‖ ≤ ∑ w, ‖x w‖ := by
  rw [homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, Prod.norm_def]
  have hs : ∀ w, ‖x w‖ ≤ ∑ w, ‖x w‖ := fun w =>
    Finset.single_le_sum (f := fun w => ‖x w‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  have h0 : 0 ≤ ∑ w, ‖x w‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine max_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun v => ?_
    rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).norm_map_of_map_zero
      (map_zero _)]
    exact hs v
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun v => ?_
    rw [(InfinitePlace.Completion.isometry_extensionEmbedding v.1).norm_map_of_map_zero
      (map_zero _)]
    exact hs v

variable {n : ℕ}

def infNorm (X : Matrix (Fin n) (Fin n) 𝔸[K]) : ℝ :=
  ∑ i, ∑ j, ∑ w : InfinitePlace K, ‖(X i j).1 w‖

theorem infNorm_nonneg (X : Matrix (Fin n) (Fin n) 𝔸[K]) : 0 ≤ infNorm X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    norm_nonneg _

theorem norm_apply_le_infNorm (X : Matrix (Fin n) (Fin n) 𝔸[K]) (i j : Fin n)
    (w : InfinitePlace K) : ‖(X i j).1 w‖ ≤ infNorm X := by
  unfold infNorm
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ∑ w : InfinitePlace K,
    ‖(X i j).1 w‖) (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      norm_nonneg _) (Finset.mem_univ i))
  refine le_trans ?_ (Finset.single_le_sum (f := fun j => ∑ w : InfinitePlace K,
    ‖(X i j).1 w‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j))
  exact Finset.single_le_sum (f := fun w : InfinitePlace K => ‖(X i j).1 w‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ w)

theorem mul_apply_fst_apply (X Y : Matrix (Fin n) (Fin n) 𝔸[K]) (i j : Fin n)
    (w : InfinitePlace K) : ((X * Y) i j).1 w = ∑ k, (X i k).1 w * (Y k j).1 w := by
  change Reduction.infEval w ((X * Y) i j) = ∑ k, Reduction.infEval w (X i k) * Reduction.infEval w (Y k j)
  rw [Matrix.mul_apply, map_sum]
  simp only [map_mul]

theorem infNorm_mul_le (X Y : Matrix (Fin n) (Fin n) 𝔸[K]) :
    infNorm (X * Y) ≤ infNorm X * infNorm Y := by
  have key : ∀ i j (w : InfinitePlace K),
      ‖((X * Y) i j).1 w‖ ≤ ∑ k, ‖(X i k).1 w‖ * ‖(Y k j).1 w‖ := fun i j w => by
    rw [mul_apply_fst_apply]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun k _ => norm_mul _ _
  set B : Fin n → ℝ := fun j => ∑ k, ∑ w : InfinitePlace K, ‖(Y k j).1 w‖ with hB
  have hb : ∀ k j (w : InfinitePlace K), ‖(Y k j).1 w‖ ≤ B j := fun k j w => by
    refine le_trans ?_ (Finset.single_le_sum (f := fun k => ∑ w : InfinitePlace K,
      ‖(Y k j).1 w‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k))
    exact Finset.single_le_sum (f := fun w : InfinitePlace K => ‖(Y k j).1 w‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  have hBsum : ∑ j, B j = infNorm Y := by
    simp only [hB, infNorm]
    exact Finset.sum_comm
  have hA : ∑ i, ∑ w : InfinitePlace K, ∑ k, ‖(X i k).1 w‖ = infNorm X := by
    simp only [infNorm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  calc infNorm (X * Y) ≤ ∑ i, ∑ j, ∑ w : InfinitePlace K, ∑ k, ‖(X i k).1 w‖ * B j :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun w _ =>
          (key i j w).trans (Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (hb k j w) (norm_nonneg _))
    _ = (∑ i, ∑ w : InfinitePlace K, ∑ k, ‖(X i k).1 w‖) * ∑ j, B j := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_mul]
    _ = infNorm X * infNorm Y := by rw [hA, hBsum]

theorem infNorm_smul {a : 𝔸[K]} {ρ : ℝ} (ha : ∀ w, ‖a.1 w‖ = ρ) (X : Matrix (Fin n) (Fin n) 𝔸[K]) :
    infNorm (a • X) = ρ * infNorm X := by
  unfold infNorm
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun w _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  change ‖a.1 w * (X i j).1 w‖ = _
  rw [norm_mul, ha w]

theorem infNorm_le_norm_infPartPi (X : Matrix (Fin n) (Fin n) 𝔸[K]) :
    infNorm X ≤ (n * n * Fintype.card (InfinitePlace K) : ℝ) *
      ‖infPartPi (matrixCoordEquiv X)‖ := by
  have h : ∀ i j (w : InfinitePlace K), ‖(X i j).1 w‖ ≤ ‖infPartPi (matrixCoordEquiv X)‖ :=
    fun i j w => (norm_apply_le_norm_homeomorphMixedSpace _ w).trans
      (norm_le_pi_norm (infPartPi (matrixCoordEquiv X)) (i, j))
  calc infNorm X ≤ ∑ _i : Fin n, ∑ _j : Fin n, ∑ _w : InfinitePlace K,
        ‖infPartPi (matrixCoordEquiv X)‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun w _ =>
          h i j w
    _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring

theorem norm_embPi_le_infNorm (ξ : Matrix (Fin n) (Fin n) K) :
    ‖embPi K (matrixCoordEquiv ξ)‖ ≤ infNorm (ratMat ξ) := by
  refine (pi_norm_le_iff_of_nonneg (infNorm_nonneg _)).2 fun p => ?_
  have h1 : embPi K (matrixCoordEquiv ξ) p =
      homeomorphMixedSpace K (algebraMap K (InfiniteAdeleRing K) (ξ p.1 p.2)) := by
    rw [homeomorphMixedSpace_algebraMap]; rfl
  rw [h1]
  refine (norm_homeomorphMixedSpace_le_sum _).trans ?_
  have h2 : ∀ w : InfinitePlace K, ‖(algebraMap K (InfiniteAdeleRing K) (ξ p.1 p.2)) w‖ =
      ‖(ratMat ξ p.1 p.2).1 w‖ := fun w => rfl
  simp only [h2]
  unfold infNorm
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ∑ w : InfinitePlace K,
    ‖(ratMat ξ i j).1 w‖) (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      norm_nonneg _) (Finset.mem_univ p.1))
  exact Finset.single_le_sum (f := fun j => ∑ w : InfinitePlace K, ‖(ratMat ξ p.1 j).1 w‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ p.2)

section Majorant

variable {ι : Type*} [Fintype ι]

theorem exists_majorant_pi {F : (ι → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhatPi K ι) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L : Set (ι → 𝔸ᶠ[K]), IsCompact L ∧ ∀ x,
      ‖F x‖ ≤ C * ((1 + ‖infPartPi x‖) ^ M)⁻¹ * L.indicator (fun _ => (1 : ℝ)) (finPartPi x) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_le_inv_one_add_pow φ M
    have hgc : Continuous g := ((mem_finiteSchwartzBruhatPi K).mp hg).1.continuous
    have hgs : HasCompactSupport g := ((mem_finiteSchwartzBruhatPi K).mp hg).2
    obtain ⟨C₂, h₂⟩ := hgc.bounded_above_of_compact_support hgs
    refine ⟨C₁ * max C₂ 0, mul_nonneg hC₁ (le_max_right _ _), tsupport g, hgs.isCompact,
      fun x => ?_⟩
    simp only [schwartzBruhatTensorPi, norm_mul]
    by_cases hx : finPartPi x ∈ tsupport g
    · rw [indicator_of_mem hx, mul_one]
      calc ‖φ (infPartPi x)‖ * ‖g (finPartPi x)‖
          ≤ (C₁ * ((1 + ‖infPartPi x‖) ^ M)⁻¹) * max C₂ 0 :=
            mul_le_mul (h₁ _) ((h₂ _).trans (le_max_left _ _)) (norm_nonneg _)
              (mul_nonneg hC₁ (inv_nonneg.2 (by positivity)))
        _ = C₁ * max C₂ 0 * ((1 + ‖infPartPi x‖) ^ M)⁻¹ := by ring
    · rw [indicator_of_notMem hx, mul_zero, image_eq_zero_of_notMem_tsupport hx, norm_zero,
        mul_zero]
  | zero =>
    exact ⟨0, le_rfl, ∅, isCompact_empty, fun x => by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨C₁, hC₁, L₁, hL₁, h₁⟩ := hG
    obtain ⟨C₂, hC₂, L₂, hL₂, h₂⟩ := hH
    refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, L₁ ∪ L₂, hL₁.union hL₂, fun x => ?_⟩
    have hi₁ : L₁.indicator (fun _ => (1 : ℝ)) (finPartPi x) ≤
        (L₁ ∪ L₂).indicator (fun _ => (1 : ℝ)) (finPartPi x) :=
      indicator_le_indicator_of_subset subset_union_left (fun _ => zero_le_one) _
    have hi₂ : L₂.indicator (fun _ => (1 : ℝ)) (finPartPi x) ≤
        (L₁ ∪ L₂).indicator (fun _ => (1 : ℝ)) (finPartPi x) :=
      indicator_le_indicator_of_subset subset_union_right (fun _ => zero_le_one) _
    have hp : 0 ≤ ((1 + ‖infPartPi x‖) ^ M)⁻¹ := inv_nonneg.2 (by positivity)
    calc ‖(G + H) x‖ ≤ ‖G x‖ + ‖H x‖ := norm_add_le _ _
      _ ≤ C₁ * ((1 + ‖infPartPi x‖) ^ M)⁻¹ * L₁.indicator (fun _ => (1 : ℝ)) (finPartPi x) +
          C₂ * ((1 + ‖infPartPi x‖) ^ M)⁻¹ * L₂.indicator (fun _ => (1 : ℝ)) (finPartPi x) :=
          add_le_add (h₁ x) (h₂ x)
      _ ≤ C₁ * ((1 + ‖infPartPi x‖) ^ M)⁻¹ *
            (L₁ ∪ L₂).indicator (fun _ => (1 : ℝ)) (finPartPi x) +
          C₂ * ((1 + ‖infPartPi x‖) ^ M)⁻¹ *
            (L₁ ∪ L₂).indicator (fun _ => (1 : ℝ)) (finPartPi x) :=
          add_le_add (mul_le_mul_of_nonneg_left hi₁ (mul_nonneg hC₁ hp))
            (mul_le_mul_of_nonneg_left hi₂ (mul_nonneg hC₂ hp))
      _ = (C₁ + C₂) * ((1 + ‖infPartPi x‖) ^ M)⁻¹ *
            (L₁ ∪ L₂).indicator (fun _ => (1 : ℝ)) (finPartPi x) := by ring
  | smul c G _ hG =>
    obtain ⟨C, hC, L, hL, h⟩ := hG
    refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC, L, hL, fun x => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((h x).trans (le_of_eq (by ring))) (norm_nonneg c)

end Majorant

variable {n : ℕ}

def IsInBox (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (X : Matrix (Fin n) (Fin n) 𝔸[K]) : Prop :=
  ∀ i j, (X i j).2 ∈ idealFiniteAdeles I

theorem exists_majorant {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∀ X : Matrix (Fin n) (Fin n) 𝔸[K],
      ‖Φ X‖ ≤ C * ((1 + infNorm X) ^ M)⁻¹ * (if IsInBox I X then 1 else 0) := by
  obtain ⟨C, hC, L, hL, h⟩ := exists_majorant_pi (mem_matrixSchwartzBruhat.mp hΦ) M
  set L' : Set 𝔸ᶠ[K] := ⋃ p : Fin n × Fin n, (fun q => q p) '' L with hL'
  have hL'c : IsCompact L' := isCompact_iUnion fun p => hL.image (continuous_apply p)
  obtain ⟨I, hI⟩ := exists_subset_idealFiniteAdeles hL'c
  set c : ℝ := max 1 (n * n * Fintype.card (InfinitePlace K) : ℝ) with hc
  have hc1 : 1 ≤ c := le_max_left _ _
  refine ⟨C * c ^ M, mul_nonneg hC (pow_nonneg (zero_le_one.trans hc1) _), I, fun X => ?_⟩
  have hX : Φ X = (fun z => Φ (Matrix.of fun i j => z (i, j))) (matrixCoordEquiv X) := rfl
  rw [hX]
  refine (h _).trans ?_
  set a := ‖infPartPi (matrixCoordEquiv X)‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ infNorm X := infNorm_nonneg X
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have h1 : 1 + infNorm X ≤ c * (1 + a) := by
    have := infNorm_le_norm_infPartPi X
    have h2 : (n * n * Fintype.card (InfinitePlace K) : ℝ) ≤ c := le_max_right _ _
    nlinarith
  have hinf : ((1 + a) ^ M)⁻¹ ≤ c ^ M * ((1 + infNorm X) ^ M)⁻¹ :=
    calc ((1 + a) ^ M)⁻¹ = c ^ M * ((c * (1 + a)) ^ M)⁻¹ := by
          rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hc0.ne'), one_mul]
      _ ≤ c ^ M * ((1 + infNorm X) ^ M)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity)
            h1 M)) (by positivity)
  have hind : L.indicator (fun _ => (1 : ℝ)) (finPartPi (matrixCoordEquiv X)) ≤
      (if IsInBox I X then 1 else 0) := by
    by_cases hmem : finPartPi (matrixCoordEquiv X) ∈ L
    · have hbox : IsInBox I X := fun i j => hI (mem_iUnion.2 ⟨(i, j), _, hmem, rfl⟩)
      rw [indicator_of_mem hmem, if_pos hbox]
    · rw [indicator_of_notMem hmem]
      split_ifs <;> norm_num
  calc C * ((1 + a) ^ M)⁻¹ * L.indicator (fun _ => (1 : ℝ)) (finPartPi (matrixCoordEquiv X))
      ≤ C * (c ^ M * ((1 + infNorm X) ^ M)⁻¹) * (if IsInBox I X then 1 else 0) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hinf hC) hind
          (indicator_nonneg (fun _ _ => zero_le_one) _) (mul_nonneg hC (by positivity))
    _ = C * c ^ M * ((1 + infNorm X) ^ M)⁻¹ * (if IsInBox I X then 1 else 0) := by ring

def finMat (X : Matrix (Fin n) (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸ᶠ[K] :=
  X.map (RingHom.snd (InfiniteAdeleRing K) 𝔸ᶠ[K])

theorem finMat_apply (X : Matrix (Fin n) (Fin n) 𝔸[K]) (i j : Fin n) : finMat X i j = (X i j).2 :=
  rfl

theorem finMat_mul (X Y : Matrix (Fin n) (Fin n) 𝔸[K]) : finMat (X * Y) = finMat X * finMat Y :=
  Matrix.map_mul

theorem continuous_finMat : Continuous (finMat (K := K) (n := n)) :=
  continuous_id.matrix_map continuous_snd

theorem exists_ideal_mul_mul {Q : Set (Matrix (Fin n) (Fin n) 𝔸ᶠ[K])} (hQ : IsCompact Q)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ∃ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      ∀ a ∈ Q, ∀ b ∈ Q, ∀ X : Matrix (Fin n) (Fin n) 𝔸ᶠ[K],
        (∀ i j, X i j ∈ idealFiniteAdeles I) → ∀ i j, (a * X * b) i j ∈ idealFiniteAdeles J := by
  set B : Set (Matrix (Fin n) (Fin n) 𝔸ᶠ[K]) :=
    Set.pi univ fun _ => Set.pi univ fun _ => (idealFiniteAdeles I : Set 𝔸ᶠ[K]) with hB
  have hBc : IsCompact B :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_idealFiniteAdeles I
  set S : Set 𝔸ᶠ[K] := ⋃ p : Fin n × Fin n,
    (fun q : (Matrix (Fin n) (Fin n) 𝔸ᶠ[K] × Matrix (Fin n) (Fin n) 𝔸ᶠ[K]) ×
        Matrix (Fin n) (Fin n) 𝔸ᶠ[K] => (q.1.1 * q.2 * q.1.2) p.1 p.2) '' ((Q ×ˢ Q) ×ˢ B)
    with hS
  have hSc : IsCompact S := by
    refine isCompact_iUnion fun p => ((hQ.prod hQ).prod hBc).image ?_
    have hm : Continuous fun q : (Matrix (Fin n) (Fin n) 𝔸ᶠ[K] ×
        Matrix (Fin n) (Fin n) 𝔸ᶠ[K]) × Matrix (Fin n) (Fin n) 𝔸ᶠ[K] => q.1.1 * q.2 * q.1.2 :=
      ((continuous_fst.comp continuous_fst).matrix_mul continuous_snd).matrix_mul
        (continuous_snd.comp continuous_fst)
    exact (continuous_apply p.2).comp ((continuous_apply p.1).comp hm)
  obtain ⟨J, hJ⟩ := exists_subset_idealFiniteAdeles hSc
  refine ⟨J, fun a ha b hb X hX i j => hJ (mem_iUnion.2 ⟨(i, j), ((a, b), X), ⟨⟨ha, hb⟩,
    fun i _ => fun j _ => hX i j⟩, rfl⟩)⟩

def latticeWeight (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (M : ℕ) (ξ : Matrix (Fin n) (Fin n) K) : ℝ :=
  if ∀ i j, ξ i j ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then ((1 + infNorm (ratMat ξ)) ^ M)⁻¹ else 0

theorem latticeWeight_nonneg (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (M : ℕ)
    (ξ : Matrix (Fin n) (Fin n) K) : 0 ≤ latticeWeight J M ξ := by
  unfold latticeWeight
  split_ifs
  · exact inv_nonneg.2 (pow_nonneg (by linarith [infNorm_nonneg (ratMat ξ)]) _)
  · exact le_rfl

theorem summable_latticeWeight (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {M : ℕ}
    (hM : Module.finrank ℝ (Fin n × Fin n → mixedEmbedding.mixedSpace K) < M) :
    Summable (latticeWeight (n := n) J M) := by
  set L := idealLatticePi (K := K) (fun _ : Fin n × Fin n => J) with hL
  have hrank : Module.finrank ℤ L < M := by rw [ZLattice.rank ℝ L]; exact hM
  have hsL : Summable fun z : L => ((1 + ‖(z : Fin n × Fin n → mixedEmbedding.mixedSpace K)‖) ^ M)⁻¹ := by
    have hs := ZLattice.summable_norm_pow_inv L M hrank
    refine Summable.of_norm_bounded_eventually hs ?_
    filter_upwards [(Set.finite_singleton (0 : L)).compl_mem_cofinite] with z hz
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [Real.norm_of_nonneg (inv_nonneg.2 (by positivity)), inv_pow]
    gcongr
    change ‖(z : Fin n × Fin n → mixedEmbedding.mixedSpace K)‖ ≤ _
    linarith [show ‖z‖ = ‖(z : Fin n × Fin n → mixedEmbedding.mixedSpace K)‖ from rfl]
  set T : Set (Matrix (Fin n) (Fin n) K) := {ξ | ∀ i j, ξ i j ∈ (J : FractionalIdeal (𝓞 K)⁰ K)}
  have hmem : ∀ ξ : T, embPi K (matrixCoordEquiv (ξ : Matrix (Fin n) (Fin n) K)) ∈ L := by
    intro ξ
    rw [hL, mem_idealLatticePi]
    intro p
    exact (mixedEmbedding.mem_idealLattice K J).2 ⟨_, ξ.2 p.1 p.2, rfl⟩
  set e : T → L := fun ξ => ⟨_, hmem ξ⟩ with he
  have he_inj : Function.Injective e := by
    intro ξ η h
    have h1 := congrArg (fun z : L => (z : Fin n × Fin n → mixedEmbedding.mixedSpace K)) h
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    have h2 := congrFun h1 (i, j)
    exact (mixedEmbedding K).injective h2
  have hsT : Summable fun ξ : T => ((1 + ‖((e ξ : L) : Fin n × Fin n →
      mixedEmbedding.mixedSpace K)‖) ^ M)⁻¹ := hsL.comp_injective he_inj
  have hsT' : Summable fun ξ : T => ((1 + infNorm (ratMat (ξ : Matrix (Fin n) (Fin n) K))) ^ M)⁻¹ := by
    have h0 : ∀ ξ : T, 0 ≤ ((1 + infNorm (ratMat (ξ : Matrix (Fin n) (Fin n) K))) ^ M)⁻¹ :=
      fun ξ => inv_nonneg.2 (pow_nonneg (by
        have := infNorm_nonneg (ratMat (ξ : Matrix (Fin n) (Fin n) K)); linarith) _)
    refine hsT.of_nonneg_of_le h0 fun ξ => ?_
    refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ M)
    have := norm_embPi_le_infNorm (ξ : Matrix (Fin n) (Fin n) K)
    change 1 + ‖embPi K (matrixCoordEquiv (ξ : Matrix (Fin n) (Fin n) K))‖ ≤ _
    linarith
  have heq : latticeWeight (n := n) J M =
      T.indicator fun ξ => ((1 + infNorm (ratMat ξ)) ^ M)⁻¹ := by
    funext ξ
    unfold latticeWeight
    by_cases h : ∀ i j, ξ i j ∈ (J : FractionalIdeal (𝓞 K)⁰ K)
    · rw [if_pos h, indicator_of_mem (show ξ ∈ T from h)]
    · rw [if_neg h, indicator_of_notMem (show ξ ∉ T from h)]
  rw [heq, ← summable_subtype_iff_indicator]
  exact hsT'

def twistedWeight (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (M : ℕ) (x y : AdelicGLn.AdelicGL K n)
    (ξ : Matrix (Fin n) (Fin n) K) : ℝ :=
  ((1 + infNorm (((x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
      (y : Matrix (Fin n) (Fin n) 𝔸[K]))) ^ M)⁻¹ *
    (if IsInBox I (((x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
      (y : Matrix (Fin n) (Fin n) 𝔸[K])) then 1 else 0)

theorem twistedWeight_nonneg (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (M : ℕ)
    (x y : AdelicGLn.AdelicGL K n) (ξ : Matrix (Fin n) (Fin n) K) : 0 ≤ twistedWeight I M x y ξ := by
  unfold twistedWeight
  refine mul_nonneg (inv_nonneg.2 (pow_nonneg ?_ _)) (by split_ifs <;> norm_num)
  linarith [infNorm_nonneg (((x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
    ratMat ξ * (y : Matrix (Fin n) (Fin n) 𝔸[K]))]

theorem ratMat_apply_snd (ξ : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (ratMat ξ i j).2 = algebraMap K 𝔸ᶠ[K] (ξ i j) :=
  adeleRing_algebraMap_snd _

theorem twistedWeight_le {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {Q : Set (Matrix (Fin n) (Fin n) 𝔸ᶠ[K])}
    (hJ : ∀ a ∈ Q, ∀ b ∈ Q, ∀ X : Matrix (Fin n) (Fin n) 𝔸ᶠ[K],
        (∀ i j, X i j ∈ idealFiniteAdeles I) → ∀ i j, (a * X * b) i j ∈ idealFiniteAdeles J)
    (M : ℕ) {x y : AdelicGLn.AdelicGL K n} (hx : finMat (x : Matrix (Fin n) (Fin n) 𝔸[K]) ∈ Q)
    (hy : finMat ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) ∈ Q)
    (ξ : Matrix (Fin n) (Fin n) K) :
    twistedWeight I M x y ξ ≤ ((1 + infNorm (x : Matrix (Fin n) (Fin n) 𝔸[K])) *
      (1 + infNorm ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))) ^ M *
        latticeWeight J M ξ := by
  obtain ⟨W, hW⟩ : ∃ W, W = ((x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
      ratMat ξ * (y : Matrix (Fin n) (Fin n) 𝔸[K]) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = infNorm (x : Matrix (Fin n) (Fin n) 𝔸[K]) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = infNorm ((y⁻¹ : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) 𝔸[K]) := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have ha0 : 0 ≤ a := ha ▸ infNorm_nonneg _
  have hb0 : 0 ≤ b := hb ▸ infNorm_nonneg _
  have hw0 : 0 ≤ infNorm W := infNorm_nonneg _
  rw [twistedWeight, ← hW]
  by_cases hbox : IsInBox I W
  · rw [if_pos hbox, mul_one]
    have hξ : ratMat ξ = (x : Matrix (Fin n) (Fin n) 𝔸[K]) * W *
        ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) := by
      rw [hW, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
        Units.mul_inv, Matrix.one_mul]
    have hmemJ : ∀ i j, ξ i j ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
      intro i j
      have h1 := hJ _ hx _ hy (finMat W) (fun i j => hbox i j) i j
      rw [← finMat_mul, ← finMat_mul, ← hξ, finMat_apply, ratMat_apply_snd] at h1
      exact (algebraMap_mem_idealFiniteAdeles_iff J _).1 h1
    have hlw : latticeWeight J M ξ = ((1 + infNorm (ratMat ξ)) ^ M)⁻¹ := by
      unfold latticeWeight; rw [if_pos hmemJ]
    rw [hlw]
    have hR : infNorm (ratMat ξ) ≤ a * infNorm W * b := by
      rw [hξ, ha, hb]
      exact (infNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (infNorm_mul_le _ _)
        (infNorm_nonneg _))
    have hR0 : 0 ≤ infNorm (ratMat ξ) := infNorm_nonneg _
    have h1 : 1 + infNorm (ratMat ξ) ≤ (1 + a) * (1 + b) * (1 + infNorm W) := by
      nlinarith [mul_nonneg ha0 hb0, mul_nonneg (mul_nonneg ha0 hb0) hw0, mul_nonneg ha0 hw0,
        mul_nonneg hb0 hw0]
    have hpos : 0 < (1 + a) * (1 + b) := mul_pos (by linarith) (by linarith)
    have hRp : 0 < 1 + infNorm (ratMat ξ) := by linarith
    have hWp : 0 < 1 + infNorm W := by linarith
    calc ((1 + infNorm W) ^ M)⁻¹ = ((1 + a) * (1 + b)) ^ M *
          (((1 + a) * (1 + b) * (1 + infNorm W)) ^ M)⁻¹ := by
          rw [mul_pow ((1 + a) * (1 + b)), mul_inv, ← mul_assoc, mul_inv_cancel₀
            (pow_ne_zero _ hpos.ne'), one_mul]
      _ ≤ ((1 + a) * (1 + b)) ^ M * ((1 + infNorm (ratMat ξ)) ^ M)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos hRp M) (pow_le_pow_left₀ hRp.le
            h1 M)) (pow_nonneg hpos.le M)
  · rw [if_neg hbox, mul_zero]
    exact mul_nonneg (pow_nonneg (mul_nonneg (by linarith) (by linarith)) M)
      (latticeWeight_nonneg J M ξ)

theorem exists_tsum_twistedWeight_le {Q : Set (Matrix (Fin n) (Fin n) 𝔸ᶠ[K])} (hQ : IsCompact Q)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {M : ℕ}
    (hM : Module.finrank ℝ (Fin n × Fin n → mixedEmbedding.mixedSpace K) < M) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ x y : AdelicGLn.AdelicGL K n,
      finMat (x : Matrix (Fin n) (Fin n) 𝔸[K]) ∈ Q →
      finMat ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) ∈ Q →
      Summable (twistedWeight I M x y) ∧
      ∑' ξ, twistedWeight I M x y ξ ≤ ((1 + infNorm (x : Matrix (Fin n) (Fin n) 𝔸[K])) *
        (1 + infNorm ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))) ^ M * S := by
  obtain ⟨J, hJ⟩ := exists_ideal_mul_mul hQ I
  have hs := summable_latticeWeight (n := n) J hM
  refine ⟨∑' ξ : Matrix (Fin n) (Fin n) K, latticeWeight J M ξ, tsum_nonneg (latticeWeight_nonneg J M), fun x y hx hy => ?_⟩
  have hle := twistedWeight_le hJ M hx hy
  have hs' := hs.mul_left (((1 + infNorm (x : Matrix (Fin n) (Fin n) 𝔸[K])) *
      (1 + infNorm ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))) ^ M)
  have hsum : Summable (twistedWeight I M x y) :=
    hs'.of_nonneg_of_le (twistedWeight_nonneg I M x y) hle
  refine ⟨hsum, (hsum.tsum_le_tsum hle hs').trans (le_of_eq (tsum_mul_left))⟩

def centralScale (n : ℕ) (t : {r : ℝ // 0 < r}) : ℝ :=
  (t : ℝ) ^ ((n * Module.finrank ℚ K : ℝ))⁻¹

theorem centralScale_pos (n : ℕ) (t : {r : ℝ // 0 < r}) : 0 < centralScale (K := K) n t :=
  Real.rpow_pos_of_pos t.2 _

theorem exists_centralSection_mul_eq (t : {r : ℝ // 0 < r}) :
    ∃ a : 𝔸[K], (∀ w, ‖a.1 w‖ = centralScale (K := K) n t) ∧ a.2 = 1 ∧
      ∀ X : Matrix (Fin n) (Fin n) 𝔸[K],
        ((Reduction.centralSection K n t : AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) 𝔸[K]) * X = a • X := by
  set a : 𝔸[K] := ((Reduction.posIdele (centralScale (K := K) n t) (centralScale_pos n t) :
    IdeleGroup K) : 𝔸[K]) with ha
  refine ⟨a, fun w => Reduction.norm_posIdele_infinite _ _ w, ?_, fun X => ?_⟩
  · ext v
    have h := Reduction.posIdele_finite (K := K) (centralScale (K := K) n t)
      (centralScale_pos (K := K) n t) v
    rw [ha, h]
    rfl
  · rw [Matrix.smul_eq_diagonal_mul]
    rfl

theorem isInBox_smul_iff {a : 𝔸[K]} (ha : a.2 = 1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (X : Matrix (Fin n) (Fin n) 𝔸[K]) : IsInBox I (a • X) ↔ IsInBox I X := by
  unfold IsInBox
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.smul_apply, smul_eq_mul, show (a * X i j).2 = a.2 * (X i j).2 from rfl, ha, one_mul]

theorem inv_one_add_mul_pow_le {ρ w : ℝ} (hρ : 0 < ρ) (hw : 0 ≤ w) (M : ℕ) :
    ((1 + ρ * w) ^ M)⁻¹ ≤ (max 1 ρ⁻¹) ^ M * ((1 + w) ^ M)⁻¹ := by
  have hm1 : 1 ≤ max 1 ρ⁻¹ := le_max_left _ _
  have hm0 : 0 < max 1 ρ⁻¹ := zero_lt_one.trans_le hm1
  have hmρ : 1 ≤ max 1 ρ⁻¹ * ρ := by
    rcases le_total 1 ρ⁻¹ with h | h
    · rw [max_eq_right h, inv_mul_cancel₀ hρ.ne']
    · rw [max_eq_left h, one_mul]
      exact (inv_le_one₀ hρ).1 h
  have h1 : 1 + w ≤ max 1 ρ⁻¹ * (1 + ρ * w) := by nlinarith
  have hp : 0 < 1 + ρ * w := by positivity
  calc ((1 + ρ * w) ^ M)⁻¹ = (max 1 ρ⁻¹) ^ M * ((max 1 ρ⁻¹ * (1 + ρ * w)) ^ M)⁻¹ := by
        rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hm0.ne'), one_mul]
    _ ≤ (max 1 ρ⁻¹) ^ M * ((1 + w) ^ M)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity)
          h1 M)) (by positivity)

theorem inv_one_add_mul_pow_add_le {ρ w c : ℝ} (hρ : 1 ≤ ρ) (hc : 0 < c) (hw : c ≤ w)
    (M M' : ℕ) : ((1 + ρ * w) ^ (M + M'))⁻¹ ≤ ((ρ * c) ^ M')⁻¹ * ((1 + w) ^ M)⁻¹ := by
  have hw0 : 0 ≤ w := hc.le.trans hw
  have h1 : 1 + w ≤ 1 + ρ * w := by nlinarith
  have h2 : ρ * c ≤ 1 + ρ * w := by nlinarith
  have hρc : 0 < ρ * c := mul_pos (zero_lt_one.trans_le hρ) hc
  rw [pow_add, mul_inv, mul_comm]
  exact mul_le_mul (inv_anti₀ (pow_pos hρc M') (pow_le_pow_left₀ hρc.le h2 M'))
    (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 M)) (by positivity)
    (by positivity)

theorem norm_le_twistedWeight {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} {C : ℝ} (hC : 0 ≤ C)
    {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {M : ℕ}
    (hmaj : ∀ X, ‖Φ X‖ ≤ C * ((1 + infNorm X) ^ M)⁻¹ * (if IsInBox I X then 1 else 0))
    (t : {r : ℝ // 0 < r}) (x y : AdelicGLn.AdelicGL K n) (ξ : Matrix (Fin n) (Fin n) K) :
    ‖Φ (((Reduction.centralSection K n t * x⁻¹ : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (y : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤
      C * (max 1 (centralScale (K := K) n t)⁻¹) ^ M * twistedWeight I M x y ξ := by
  obtain ⟨a, ha1, ha2, hmul⟩ := exists_centralSection_mul_eq (K := K) (n := n) t
  set W := ((x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
    (y : Matrix (Fin n) (Fin n) 𝔸[K]) with hW
  have heq : ((Reduction.centralSection K n t * x⁻¹ : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (y : Matrix (Fin n) (Fin n) 𝔸[K]) = a • W := by
    rw [Units.val_mul, hW, ← hmul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [heq]
  refine (hmaj _).trans ?_
  rw [infNorm_smul ha1, isInBox_smul_iff ha2]
  unfold twistedWeight
  rw [← hW]
  have hb : (0 : ℝ) ≤ if IsInBox I W then 1 else 0 := by split_ifs <;> norm_num
  calc C * ((1 + centralScale n t * infNorm W) ^ M)⁻¹ * (if IsInBox I W then 1 else 0)
      ≤ C * ((max 1 (centralScale (K := K) n t)⁻¹) ^ M * ((1 + infNorm W) ^ M)⁻¹) *
          (if IsInBox I W then 1 else 0) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (inv_one_add_mul_pow_le
          (centralScale_pos n t) (infNorm_nonneg W) M) hC) hb
    _ = _ := by ring

theorem norm_det_le_of_mem {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    {t : v.adicCompletion K} (ht : t ≠ 0) {A : Matrix (Fin n) (Fin n) (v.adicCompletion K)}
    (hA : ∀ i j, t⁻¹ * A i j ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) :
    ‖A.det‖ ≤ ‖t‖ ^ n := by
  set O := IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
  set A' : Matrix (Fin n) (Fin n) O := fun i j => ⟨t⁻¹ * A i j, hA i j⟩
  have hmap : A'.map O.subtype = t⁻¹ • A := by
    ext i j; rfl
  have hdet : (t⁻¹ • A).det ∈ O := by
    have h := RingHom.map_det O.subtype A'
    rw [RingHom.mapMatrix_apply, hmap] at h
    rw [← h]
    exact (A'.det).2
  rw [Matrix.det_smul, Fintype.card_fin] at hdet
  have h1 := Reduction.norm_le_one_of_mem v hdet
  rw [norm_mul, norm_pow, norm_inv] at h1
  have htp : 0 < ‖t‖ ^ n := pow_pos (norm_pos_iff.2 ht) n
  rw [inv_pow, inv_mul_le_iff₀ htp, mul_one] at h1
  exact h1

theorem exists_le_infNorm_of_isInBox (hn : 0 < n) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ W : AdelicGLn.AdelicGL K n, (Reduction.detModule K n W : ℝ) = 1 →
      IsInBox I (W : Matrix (Fin n) (Fin n) 𝔸[K]) →
        c₀ ≤ infNorm (W : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  set tI := idealIdele I with htI
  set B : ℝ := ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ‖(tI : 𝔸ᶠ[K]) v‖ ^ n with hB
  set d := Module.finrank ℚ K with hd
  have hd1 : 1 ≤ d := Module.finrank_pos
  have hB0 : 0 ≤ B := finprod_nonneg fun _ => pow_nonneg (norm_nonneg _) _
  set D : ℝ := max B 1 * (n.factorial : ℝ) ^ d with hD
  have hD0 : 0 < D := mul_pos (zero_lt_one.trans_le (le_max_right _ _))
    (pow_pos (by exact_mod_cast Nat.factorial_pos n) d)
  refine ⟨min 1 D⁻¹, lt_min one_pos (inv_pos.2 hD0), fun W hW hbox => ?_⟩
  set X := infNorm (W : Matrix (Fin n) (Fin n) 𝔸[K]) with hX
  have hX0 : 0 ≤ X := infNorm_nonneg _
  obtain ⟨u, hu⟩ : ∃ u : IdeleGroup K, u = AdelicGLn.det K n W := ⟨_, rfl⟩
  have hu1 : (IdeleGroup.ideleModule K u : ℝ) = 1 := hu ▸ hW
  rw [IdeleGroup.ideleModule_eq] at hu1

  have hfin : ∀ v, ‖((u : 𝔸[K])).2 v‖ ≤ ‖(tI : 𝔸ᶠ[K]) v‖ ^ n := by
    intro v
    have h1 : ((u : 𝔸[K])).2 v =
        ((W : Matrix (Fin n) (Fin n) 𝔸[K]).map (Reduction.finEval v)).det := by
      change Reduction.finEval v (u : 𝔸[K]) = _
      rw [hu, AdelicGLn.coe_det, RingHom.map_det, RingHom.mapMatrix_apply]
    rw [h1]
    have hne : (tI : 𝔸ᶠ[K]) v ≠ 0 := by
      have h := congrArg (fun a : 𝔸ᶠ[K] => a v) (Units.mul_inv tI)
      have h' : (tI : 𝔸ᶠ[K]) v * ((tI⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) v = 1 := h
      exact left_ne_zero_of_mul_eq_one h'
    refine norm_det_le_of_mem hne fun i j => ?_
    have hmem := hbox i j
    rw [← SetLike.mem_coe, idealFiniteAdeles_eq_smul, mem_units_smul_integralFiniteAdeles_iff]
      at hmem
    exact hmem v
  have hPf : ∏ᶠ v, ‖((u : 𝔸[K])).2 v‖ ≤ B := by
    refine Reduction.finprod_le_finprod_of_nonneg (IdeleGroup.finite_mulSupport_norm u) ?_
      (fun _ => norm_nonneg _) hfin
    refine (finite_mulSupport_nnnorm_units tI).subset fun v hv => ?_
    simp only [Function.mem_mulSupport] at hv ⊢
    intro h1
    apply hv
    have : ‖(tI : 𝔸ᶠ[K]) v‖ = 1 := by rw [← coe_nnnorm, h1, NNReal.coe_one]
    rw [this, one_pow]
  have hinf : ∀ w : InfinitePlace K, ‖((u : 𝔸[K])).1 w‖ ≤ (n.factorial : ℝ) * X ^ n := by
    intro w
    have h1 : ((u : 𝔸[K])).1 w =
        ((W : Matrix (Fin n) (Fin n) 𝔸[K]).map (Reduction.infEval w)).det := by
      change Reduction.infEval w (u : 𝔸[K]) = _
      rw [hu, AdelicGLn.coe_det, RingHom.map_det, RingHom.mapMatrix_apply]
    rw [h1]
    have h2 := Matrix.det_le (abv := NormedField.toAbsoluteValue w.Completion) (x := X)
      (A := (W : Matrix (Fin n) (Fin n) 𝔸[K]).map (Reduction.infEval w))
      (fun i j => norm_apply_le_infNorm _ i j w)
    rw [Fintype.card_fin, nsmul_eq_mul] at h2
    exact h2
  have hPinf : ∏ w : InfinitePlace K, ‖((u : 𝔸[K])).1 w‖ ^ w.mult ≤
      ((n.factorial : ℝ) * X ^ n) ^ d := by
    calc ∏ w : InfinitePlace K, ‖((u : 𝔸[K])).1 w‖ ^ w.mult
        ≤ ∏ w : InfinitePlace K, ((n.factorial : ℝ) * X ^ n) ^ w.mult :=
          Finset.prod_le_prod (fun w _ => pow_nonneg (norm_nonneg _) _)
            (fun w _ => pow_le_pow_left₀ (norm_nonneg _) (hinf w) _)
      _ = ((n.factorial : ℝ) * X ^ n) ^ d := by
          rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  have hfac0 : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
  have h1 : 1 ≤ ((n.factorial : ℝ) * X ^ n) ^ d * B := by
    rw [← hu1]
    exact mul_le_mul hPinf hPf (finprod_nonneg fun _ => norm_nonneg _)
      (pow_nonneg (mul_nonneg hfac0 (pow_nonneg hX0 _)) _)
  by_cases hX1 : 1 ≤ X
  · exact (min_le_left _ _).trans hX1
  · push Not at hX1
    have hXn : X ^ n ≤ X := pow_le_of_le_one hX0 hX1.le hn.ne'
    have hXd : X ^ d ≤ X := pow_le_of_le_one hX0 hX1.le (by omega)
    have h2 : ((n.factorial : ℝ) * X ^ n) ^ d ≤ (n.factorial : ℝ) ^ d * X := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (pow_nonneg hX0 _) hXn d).trans hXd)
        (pow_nonneg hfac0 _)
    have h3 : 1 ≤ D * X := by
      calc 1 ≤ ((n.factorial : ℝ) * X ^ n) ^ d * B := h1
        _ ≤ (n.factorial : ℝ) ^ d * X * max B 1 :=
          mul_le_mul h2 (le_max_left _ _) hB0 (mul_nonneg (pow_nonneg hfac0 _) hX0)
        _ = D * X := by rw [hD]; ring
    refine (min_le_right _ _).trans ?_
    rw [inv_le_iff_one_le_mul₀ hD0]
    linarith [mul_comm D X]

end GJGlobal

end

end GroundTheory.Automorphic
