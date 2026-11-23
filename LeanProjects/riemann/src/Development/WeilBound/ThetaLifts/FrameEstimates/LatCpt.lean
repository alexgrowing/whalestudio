import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace LatticeQuotientCompactness

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem topRing : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)

theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ) := by
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) (piInf τ) ?_
  have h : ⇑((piInf τ).comp (algebraMap (AF F) (AE F E))) =
      fun a : AF F => InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
    funext a
    change infEmb τ (compInf F E w (a ⊗ₜ[F] (1 : E))) = _
    change infEmb τ (evInf F w a ⊗ₜ[F] (1 : E)) = _
    rw [infEmb_tmul, map_one, mul_one]
    rfl
  rw [h]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst)

variable (τ : ∀ w : InfinitePlace F, EmbOver E w)

theorem continuous_sz {n d : ℕ} : Continuous (sz τ : Ten F E n d → ℝ) := by
  unfold sz
  refine continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_piInf (τ w)).comp ((continuous_apply j).comp (continuous_apply i))).norm

theorem sz_nonneg {n d : ℕ} (z : Ten F E n d) : 0 ≤ sz τ z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem entry_le_sz {n d : ℕ} (z : Ten F E n d) (w : InfinitePlace F) (i : Fin n) (j : Fin d) :
    ‖piInf (τ w) (z i j)‖ ≤ sz τ z := by
  unfold sz
  refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ i, ∑ j, ‖piInf (τ w) (z i j)‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ w))
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖piInf (τ w) (z i j)‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ‖piInf (τ w) (z i j)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

theorem sz_mul_mul_le {n d : ℕ} (A : Ten F E n n) (B : Ten F E d d) (z : Ten F E n d) :
    sz τ (A * z * Bᵀ : Ten F E n d) ≤ (n * d * (sz τ A * sz τ B)) * sz τ z := by
  have hA := sz_nonneg τ A
  have hB := sz_nonneg τ B
  have key : ∀ w i j, ‖piInf (τ w) ((A * z * Bᵀ : Ten F E n d) i j)‖ ≤
      (sz τ A * sz τ B) * ∑ k, ∑ l, ‖piInf (τ w) (z k l)‖ := by
    intro w i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul]
    have h1 := entry_le_sz τ A w i k
    have h2 := entry_le_sz τ B w j l
    calc _ ≤ sz τ A * ‖piInf (τ w) (z k l)‖ * sz τ B := by gcongr
      _ = _ := by ring
  calc sz τ (A * z * Bᵀ : Ten F E n d)
      ≤ ∑ w, ∑ _i : Fin n, ∑ _j : Fin d, (sz τ A * sz τ B) * ∑ k, ∑ l, ‖piInf (τ w) (z k l)‖ :=
        Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key w i j
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show sz τ z = ∑ w, ∑ k, ∑ l, ‖piInf (τ w) (z k l)‖ from rfl, Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => by ring

theorem maj_nonneg {n d : ℕ} (C : Set (Ten F E n d)) (N : ℕ) (z : Ten F E n d) : 0 ≤ maj τ C N z := by
  have := sz_nonneg τ z
  unfold maj
  split_ifs
  · positivity
  · exact le_rfl

theorem maj_le {n d : ℕ} (C C' : Set (Ten F E n d)) (N : ℕ) (A : Ten F E n n) (B : Ten F E d d) (K : ℝ) (hK : 1 ≤ K)
    (hAB : n * d * (sz τ A * sz τ B) ≤ K) (hC : ∀ c ∈ C, (A * c * Bᵀ : Ten F E n d) ∈ C') (z : Ten F E n d) :
    maj τ C N z ≤ K ^ N * maj τ C' N (A * z * Bᵀ : Ten F E n d) := by
  by_cases h : ∃ c ∈ C, At (evI F) (z - c)
  · have h' : ∃ c ∈ C', At (evI F) ((A * z * Bᵀ : Ten F E n d) - c) := by
      obtain ⟨c, hc, hz⟩ := h
      refine ⟨_, hC c hc, fun u hu => ?_⟩
      rw [← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.smul_mul, ← Matrix.mul_smul, hz u hu, Matrix.mul_zero,
        Matrix.zero_mul]
    unfold maj
    rw [if_pos h, if_pos h']
    have h0 := sz_nonneg τ z
    have h1 := sz_nonneg τ (A * z * Bᵀ : Ten F E n d)
    have h2 : 1 + sz τ (A * z * Bᵀ : Ten F E n d) ≤ K * (1 + sz τ z) := by
      have := (sz_mul_mul_le τ A B z).trans (mul_le_mul_of_nonneg_right hAB h0)
      linarith
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul, div_le_iff₀ (by positivity), ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 N
  · have := maj_nonneg τ C' N (A * z * Bᵀ : Ten F E n d)
    rw [maj, if_neg h]
    positivity

theorem continuous_mat {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : Continuous fun g : UA σ J => mat g :=
  Units.continuous_val.comp continuous_subtype_val

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g κ : UA σ J) : mat κ * mat (g * κ)⁻¹ = mat g⁻¹ := by
  rw [← mat_mul, mul_inv_rev, mul_inv_cancel_left]

end LatticeQuotientCompactness

open LatticeQuotientCompactness in

theorem latCpt_of : LatCpt := by
  intro F E _ _ _ _ _ σ _ τ n d J J' _ _ Ω Ω' hΩ hΩ' C N hC
  have := topRing (F := F) (E := E)
  obtain ⟨M, hM⟩ := (hΩ.image ((continuous_sz τ).comp continuous_mat)).bddAbove
  obtain ⟨M', hM'⟩ := (hΩ'.image ((continuous_sz τ).comp continuous_mat)).bddAbove
  let K : ℝ := max 1 (n * d * (M * M'))
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : 0 ≤ K ^ N := by positivity
  let f : UA σ J × Ten F E n d × UA σ J' → Ten F E n d := fun p => mat p.1 * p.2.1 * (mat p.2.2)ᵀ
  have hf : Continuous f :=
    ((continuous_mat.comp continuous_fst).matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul
      (continuous_mat.comp (continuous_snd.comp continuous_snd)).matrix_transpose
  refine ⟨f '' (Ω ×ˢ C ×ˢ Ω'), ⟨K ^ N, hK0⟩, (hΩ.prod (hC.prod hΩ')).image hf, fun S g h κ hκ κ' hκ' => ?_⟩
  unfold latSum
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  have a1 : sz τ (mat κ) ≤ M := hM ⟨κ, hκ, rfl⟩
  have a2 : sz τ (mat κ') ≤ M' := hM' ⟨κ', hκ', rfl⟩
  have b1 := sz_nonneg τ (mat κ)
  have b2 := sz_nonneg τ (mat κ')
  have hAB : n * d * (sz τ (mat κ) * sz τ (mat κ')) ≤ K := by
    refine le_trans ?_ (le_max_right _ _)
    have : 0 ≤ M := b1.trans a1
    gcongr
  have key := maj_le τ C (f '' (Ω ×ˢ C ×ˢ Ω')) N (mat κ) (mat κ') K hK hAB
    (fun c hc => ⟨(κ, c, κ'), ⟨hκ, hc, hκ'⟩, rfl⟩) (mat (g * κ)⁻¹ * incM F x.1 * (mat (h * κ')⁻¹)ᵀ)
  have e : mat κ * (mat (g * κ)⁻¹ * incM F x.1 * (mat (h * κ')⁻¹)ᵀ) * (mat κ')ᵀ =
      mat g⁻¹ * incM F x.1 * (mat h⁻¹)ᵀ := by
    rw [← mat_mul_inv g κ, ← mat_mul_inv h κ', Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [e] at key
  refine (ENNReal.ofReal_le_ofReal key).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hK0, ENNReal.ofReal_eq_coe_nnreal hK0]
  rfl

end PositivityTheory.ThKEst

end
