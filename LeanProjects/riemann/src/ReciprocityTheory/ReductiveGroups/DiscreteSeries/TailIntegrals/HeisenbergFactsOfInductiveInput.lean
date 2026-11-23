import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergRankOneDecomposition
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.RankOneLeviComm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HpkNegMp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.EIntBound

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem heisenbergFacts_of_inductiveInput (h : InductiveHeisenbergInputs) : OneStepInt ∧ OneStepCoord ∧ HeisConjLev ∧ HeisInv ∧ HeisMem ∧ HeisHaar ∧
    HaarGExists ∧ HeisAct ∧ GNLower ∧ HeisClosed ∧ HeisConjLevMeas := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27⟩ := h
  exact ⟨h1, h2, h6, h8, h10, h12, h26, h27, h16, h11, h7⟩

section cont
variable (k r' : ℕ)

theorem lift_cont : Continuous (liftVec k 1 r') := by
  refine continuous_pi fun p => ?_
  unfold liftVec
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · simp only [dif_pos hp]; exact continuous_apply _
  · simp only [dif_neg hp]; exact continuous_const

theorem heisenberg_map_continuous : Continuous (heis0 k r') := by
  have h1 : Continuous fun x : HPar k r' => liftVec k 1 r' x.1 := (lift_cont k r').comp continuous_fst
  unfold heis0 heisG hb herm
  fun_prop

theorem lev_cont : Continuous (fun g : Mat k r' => ιLev k 1 r' g) := by
  refine continuous_matrix fun p q => ?_
  unfold ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
    · simp only [dif_pos hp, dif_pos hq]; exact continuous_id.matrix_elem _ _
    · simp only [dif_pos hp, dif_neg hq]; exact continuous_const
  · simp only [dif_neg hp]; exact continuous_const

theorem Dl_cont (r : ℕ) (l : Fin (r + 1)) : Continuous (fun g : Mt k r => Dl k r l (Matrix.of g)) := by
  unfold Dl herm
  fun_prop

theorem FsE_meas (r : ℕ) (s : Fin (r + 1) → ℝ) : Measurable (fun g : Mt k r => FsE k r s (Matrix.of g)) := by
  unfold FsE
  exact Finset.measurable_prod _ fun l _ =>
    ((Dl_cont k r l).measurable.nnnorm.coe_nnreal_ennreal).pow_const _

theorem EInt_meas (A : ℝ) (c : ℂ) : Measurable (fun g : Mt k r' => EInt k r' A c (Matrix.of g)) := by
  unfold EInt
  have h1 := heisenberg_map_continuous k r'
  have h2 := lev_cont k r'
  have h3 := gN_cont k (1 + r')
  refine Measurable.lintegral_prod_right'
    (f := fun p : Mt k r' × HPar k r' =>
      ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' (Matrix.of p.1) * heis0 k r' p.2) ^ (-A))) ?_
  exact ((by fun_prop : Continuous fun p : Mt k r' × HPar k r' =>
    gN (w0 k r' c * ιLev k 1 r' (Matrix.of p.1) * heis0 k r' p.2)).measurable.pow_const _).ennreal_ofReal

theorem heis_left (hHH : HeisHaar) (F : Mt k (1 + r') → ℝ≥0∞) (hF : Measurable F) (z : HPar k r') :
    ∫⁻ x, F (heis0 k r' z * heis0 k r' x) = ∫⁻ x, F (heis0 k r' x) := by
  have hc : @Continuous (HPar k r') (Mt k (1 + r')) _ _ (fun x => heis0 k r' x) := heisenberg_map_continuous k r'
  have hm : @Measurable (HPar k r') (Mt k (1 + r')) _ _ (fun x => heis0 k r' x) := hc.measurable
  have hl : Measurable (lmulM (heis0 k r' z) : Mt k (1 + r') → Mt k (1 + r')) :=
    (by unfold lmulM; fun_prop : Continuous (lmulM (heis0 k r' z) : Mt k (1 + r') → Mt k (1 + r'))).measurable
  calc ∫⁻ x, F (heis0 k r' z * heis0 k r' x) = ∫⁻ n, F (lmulM (heis0 k r' z) n) ∂(μHeis k r') := by
        rw [μHeis]; exact (lintegral_map (hF.comp hl) hm).symm
    _ = ∫⁻ n, F n ∂((μHeis k r').map (lmulM (heis0 k r' z))) := (lintegral_map hF hl).symm
    _ = ∫⁻ n, F n ∂(μHeis k r') := by rw [(hHH k r').left _ ⟨z, rfl⟩]
    _ = ∫⁻ x, F (heis0 k r' x) := by rw [μHeis]; exact lintegral_map hF hm

theorem EInt_K (A : ℝ) (c : ℂ) {κ : Mat k r'} (hκ : κ ∈ Kset k r') (g : Mat k r') :
    EInt k r' A c (κ * g) = EInt k r' A c g := by
  unfold EInt
  refine lintegral_congr fun x => ?_
  have e : w0 k r' c * ιLev k 1 r' (κ * g) * heis0 k r' x =
      ιLev k 1 r' κ * (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) := by
    rw [lev_mul, ← Matrix.mul_assoc (w0 k r' c), rankOne_levi_comm]; simp only [Matrix.mul_assoc]
  rw [e, gN_unitary k (1 + r') (lev_K k r' hκ).2]

end cont

section inner
variable (k r' : ℕ)

def Dx (x : HPar k r') : ℝ := Real.sqrt (Ga k (1 + r') 0 (Yx k r' x))

def Psi (s : Fin (1 + r' + 1) → ℝ) (x : HPar k r') : ℝ :=
  ∏ l : Fin (r' + 1), (Ga k (1 + r') (sc r' l) (Yx k r' x) / Ga k (1 + r') 0 (Yx k r' x)) ^ (-s (sc r' l) / 2)

def Qf (A : ℝ) (s1 : Fin (r' + 1) → ℝ) (μ₁ : Measure (Mt k r')) (c : ℂ) : ℝ≥0∞ :=
  ∫⁻ g, EInt k r' A c (Matrix.of g) * FsE k r' s1 (Matrix.of g) ∂μ₁

theorem inner_eq (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hT : TLeft) (hk : 1 ≤ k) (A : ℝ) (s : Fin (1 + r' + 1) → ℝ)
    (μ₁ : Measure (Mt k r')) (hμ₁ : IsHaarOn (GV k r') μ₁) (x : HPar k r') (c : ℂ) (hc : c ≠ 0) :
    ∫⁻ g, (∫⁻ x', ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A))) *
        FsE k r' (fun l => s (sc r' l)) (Matrix.of g) ∂μ₁ =
      ENNReal.ofReal (Psi k r' s x) * Qf k r' A (fun l => s (sc r' l)) μ₁ (c * (Dx k r' x : ℂ)) := by
  obtain ⟨-, -, hHCL, -, -, hHH, -, -, -, -, -⟩ := heisenbergFacts_of_inductiveInput hB2
  obtain ⟨κ, hκ, m, hm, z, hdec, hga⟩ := heisenberg_rankOne_decomposition hB2 hIW k r' hk x c hc
  have hG0 := (yx_ga hB2 hIW k r' hk x).1
  have hdec' : (heis0 k r' x)⁻¹ * w0 k r' c =
      κ * w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' m * heis0 k r' z := hdec
  have hpt : ∀ g : Mt k r', Matrix.of g ∈ GV k r' →
      ∫⁻ x', ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A)) =
        EInt k r' A (c * (Dx k r' x : ℂ)) (m * Matrix.of g) := by
    intro g hg
    obtain ⟨z2, hz2⟩ : ∃ z2 : HPar k r', z2 = ((Matrix.of g)⁻¹ *ᵥ z.1, z.2) := ⟨_, rfl⟩
    have hcomm : heis0 k r' z * ιLev k 1 r' (Matrix.of g) = ιLev k 1 r' (Matrix.of g) * heis0 k r' z2 := by
      have h1 := hHCL k r' (Matrix.of g) hg z2
      have h2 : ((Matrix.of g *ᵥ z2.1, z2.2) : HPar k r') = z := by
        rw [hz2]; dsimp only; rw [mulVec_mulVec, UH_mul_inv k r' hg, one_mulVec]
      rw [h2] at h1
      rw [← h1, Matrix.mul_assoc, UH_inv_mul k (1 + r') (lev_mem k r' hg), Matrix.mul_one]
    have hmat : ∀ x', oneStep k r' x c (Matrix.of g) x' =
        κ * (w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' (m * Matrix.of g) * (heis0 k r' z2 * heis0 k r' x')) := by
      intro x'
      unfold oneStep
      rw [hdec', Matrix.mul_assoc (κ * w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' m) (heis0 k r' z)
        (ιLev k 1 r' (Matrix.of g)), hcomm, lev_mul]
      simp only [Matrix.mul_assoc]
    simp only [hmat, gN_unitary k (1 + r') hκ.2]
    have h3 := gN_cont k (1 + r')
    have hF : Measurable fun n : Mt k (1 + r') =>
        ENNReal.ofReal (gN (w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' (m * Matrix.of g) * Matrix.of n) ^ (-A)) :=
      ((by fun_prop : Continuous fun n : Mt k (1 + r') =>
        gN (w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' (m * Matrix.of g) * Matrix.of n)).measurable.pow_const
          _).ennreal_ofReal
    exact heis_left k r' hHH _ hF z2
  have hconc : ∀ᵐ g ∂μ₁, Matrix.of g ∈ GV k r' := by
    rw [ae_iff]; exact hμ₁.conc
  have hl : Measurable (lmulM m : Mt k r' → Mt k r') :=
    (by unfold lmulM; fun_prop : Continuous (lmulM m : Mt k r' → Mt k r')).measurable
  have hli : Measurable (lmulM m⁻¹ : Mt k r' → Mt k r') :=
    (by unfold lmulM; fun_prop : Continuous (lmulM m⁻¹ : Mt k r' → Mt k r')).measurable
  have hG : Measurable (fun g : Mt k r' => EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of g) *
      FsE k r' (fun l => s (sc r' l)) (m⁻¹ * Matrix.of g)) :=
    (EInt_meas k r' A _).mul ((FsE_meas k r' (fun l => s (sc r' l))).comp hli)
  have e : ∀ g : Mt k r', m⁻¹ * (m * Matrix.of g) = Matrix.of g := fun g => by
    rw [← Matrix.mul_assoc, UH_inv_mul k r' hm, Matrix.one_mul]
  calc ∫⁻ g, (∫⁻ x', ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A))) *
        FsE k r' (fun l => s (sc r' l)) (Matrix.of g) ∂μ₁
      = ∫⁻ g, EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of (lmulM m g)) *
          FsE k r' (fun l => s (sc r' l)) (m⁻¹ * Matrix.of (lmulM m g)) ∂μ₁ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hconc] with g hg
        rw [hpt g hg]
        show _ = EInt k r' A (c * (Dx k r' x : ℂ)) (m * Matrix.of g) *
          FsE k r' (fun l => s (sc r' l)) (m⁻¹ * (m * Matrix.of g))
        rw [e]
    _ = ∫⁻ g, EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of g) *
          FsE k r' (fun l => s (sc r' l)) (m⁻¹ * Matrix.of g) ∂(μ₁.map (lmulM m)) := (lintegral_map hG hl).symm
    _ = ∫⁻ g, EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of g) *
          FsE k r' (fun l => s (sc r' l)) (m⁻¹ * Matrix.of g) ∂μ₁ := by rw [hμ₁.left m hm]
    _ = ENNReal.ofReal (fsR k r' (fun l => s (sc r' l)) m) *
          Qf k r' A (fun l => s (sc r' l)) μ₁ (c * (Dx k r' x : ℂ)) :=
        hT k r' (fun l => s (sc r' l)) μ₁ (fun g => EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of g)) hk hμ₁
          (EInt_meas k r' A _) (fun κ' hκ' g => EInt_K k r' A _ hκ' (Matrix.of g)) m hm
    _ = ENNReal.ofReal (Psi k r' s x) * Qf k r' A (fun l => s (sc r' l)) μ₁ (c * (Dx k r' x : ℂ)) := by
        congr 1; congr 1
        unfold fsR Psi
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [eq_div_of_mul_eq hG0.ne' (hga l)]

end inner

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
