import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

noncomputable section

open GlobalTheory.CompanionTheory.ThTot

namespace GlobalTheory.CompanionTheory.ThTot.SchwT

section Analysis

variable {E E₁ E₂ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

theorem norm_iter_comp_le (A : E →L[ℝ] E₁) (hA : ‖A‖ ≤ 1) (f : SchwartzMap E₁ ℂ) (n : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ n (fun w => f (A w)) z‖ ≤ ‖iteratedFDeriv ℝ n f (A z)‖ := by
  have h : iteratedFDeriv ℝ n (fun w => f (A w)) z =
      (iteratedFDeriv ℝ n f (A z)).compContinuousLinearMap fun _ => A :=
    A.iteratedFDeriv_comp_right (f := f) (f.smooth n) z le_rfl
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _i : Fin n, ‖A‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => hA
  exact mul_le_of_le_one_right (norm_nonneg _) this

def tens (A : E →L[ℝ] E₁) (B : E →L[ℝ] E₂) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hAB : ∀ z, ‖z‖ ≤ max ‖A z‖ ‖B z‖) (f : SchwartzMap E₁ ℂ) (g : SchwartzMap E₂ ℂ) : SchwartzMap E ℂ where
  toFun z := f (A z) * g (B z)
  smooth' := ((f.smooth ⊤).comp A.contDiff).mul ((g.smooth ⊤).comp B.contDiff)
  decay' := by
    intro k n
    choose Cf hCf using fun (a : ℕ × ℕ) => f.decay' a.1 a.2
    choose Cg hCg using fun (a : ℕ × ℕ) => g.decay' a.1 a.2
    refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (Cf (k, i) * Cg (0, n - i) + Cf (0, i) * Cg (k, n - i)), fun z => ?_⟩
    have hf1 : ContDiff ℝ n (fun w => f (A w)) := (f.smooth n).comp A.contDiff
    have hg1 : ContDiff ℝ n (fun w => g (B w)) := (g.smooth n).comp B.contDiff
    have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (n := n) (N := n) hf1 hg1 z le_rfl
    have hz : ‖z‖ ^ k ≤ ‖A z‖ ^ k + ‖B z‖ ^ k := by
      rcases le_total ‖A z‖ ‖B z‖ with h | h
      · have : ‖z‖ ≤ ‖B z‖ := (hAB z).trans (max_le h le_rfl)
        exact (pow_le_pow_left₀ (norm_nonneg _) this k).trans (le_add_of_nonneg_left (by positivity))
      · have : ‖z‖ ≤ ‖A z‖ := (hAB z).trans (max_le le_rfl h)
        exact (pow_le_pow_left₀ (norm_nonneg _) this k).trans (le_add_of_nonneg_right (by positivity))
    calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun z => f (A z) * g (B z)) z‖
        ≤ ‖z‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun w => f (A w)) z‖ * ‖iteratedFDeriv ℝ (n - i) (fun w => g (B w)) z‖ :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ = ∑ i ∈ Finset.range (n + 1), ‖z‖ ^ k * ((n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun w => f (A w)) z‖ * ‖iteratedFDeriv ℝ (n - i) (fun w => g (B w)) z‖) :=
          Finset.mul_sum _ _ _
      _ ≤ _ := by
          refine Finset.sum_le_sum fun i _ => ?_
          set a := ‖iteratedFDeriv ℝ i f (A z)‖
          set b := ‖iteratedFDeriv ℝ (n - i) g (B z)‖
          have ha0 : 0 ≤ a := norm_nonneg _
          have hb0 : 0 ≤ b := norm_nonneg _
          have h1 : ‖A z‖ ^ k * a ≤ Cf (k, i) := hCf (k, i) (A z)
          have h2 : b ≤ Cg (0, n - i) := by
            have := hCg (0, n - i) (B z)
            simp only [pow_zero, one_mul] at this
            exact this
          have h3 : a ≤ Cf (0, i) := by
            have := hCf (0, i) (A z)
            simp only [pow_zero, one_mul] at this
            exact this
          have h4 : ‖B z‖ ^ k * b ≤ Cg (k, n - i) := hCg (k, n - i) (B z)
          have hn0 : (0 : ℝ) ≤ n.choose i := by positivity
          have hA' := norm_iter_comp_le A hA f i z
          have hB' := norm_iter_comp_le B hB g (n - i) z
          have hAk : 0 ≤ ‖A z‖ ^ k := by positivity
          have hBk : 0 ≤ ‖B z‖ ^ k := by positivity
          have e1 : ‖A z‖ ^ k * a * b ≤ Cf (k, i) * Cg (0, n - i) :=
            mul_le_mul h1 h2 hb0 ((mul_nonneg hAk ha0).trans h1)
          have e2 : a * (‖B z‖ ^ k * b) ≤ Cf (0, i) * Cg (k, n - i) :=
            mul_le_mul h3 h4 (mul_nonneg hBk hb0) (ha0.trans h3)
          calc ‖z‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w => f (A w)) z‖ *
                ‖iteratedFDeriv ℝ (n - i) (fun w => g (B w)) z‖)
              ≤ (‖A z‖ ^ k + ‖B z‖ ^ k) * ((n.choose i : ℝ) * a * b) := by
                refine mul_le_mul hz ?_ (by positivity) (by positivity)
                exact mul_le_mul (mul_le_mul_of_nonneg_left hA' hn0) hB' (norm_nonneg _) (by positivity)
            _ = (n.choose i : ℝ) * (‖A z‖ ^ k * a * b + a * (‖B z‖ ^ k * b)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hn0

@[simp] theorem tens_apply (A : E →L[ℝ] E₁) (B : E →L[ℝ] E₂) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hAB : ∀ z, ‖z‖ ≤ max ‖A z‖ ‖B z‖) (f : SchwartzMap E₁ ℂ) (g : SchwartzMap E₂ ℂ) (z : E) :
    tens A B hA hB hAB f g z = f (A z) * g (B z) := rfl

end Analysis

section Coord

variable {T : Type*} [Fintype T] {r s p : ℕ}

def topL (T : Type*) [Fintype T] (r s p : ℕ) : (T → Fin (r + s) → Fin p → ℂ) →L[ℝ] (T → Fin r → Fin p → ℂ) where
  toFun t := fun τ i j => t τ (Fin.castAdd s i) j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

def botL (T : Type*) [Fintype T] (r s p : ℕ) : (T → Fin (r + s) → Fin p → ℂ) →L[ℝ] (T → Fin s → Fin p → ℂ) where
  toFun t := fun τ i j => t τ (Fin.natAdd r i) j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

theorem norm_coord_le (t : T → Fin r → Fin p → ℂ) (τ : T) (i : Fin r) (j : Fin p) : ‖t τ i j‖ ≤ ‖t‖ :=
  (norm_le_pi_norm (t τ i) j).trans ((norm_le_pi_norm (t τ) i).trans (norm_le_pi_norm t τ))

theorem norm_le_of_coord {t : T → Fin r → Fin p → ℂ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ τ i j, ‖t τ i j‖ ≤ C) : ‖t‖ ≤ C :=
  (pi_norm_le_iff_of_nonneg hC).2 fun τ => (pi_norm_le_iff_of_nonneg hC).2 fun i =>
    (pi_norm_le_iff_of_nonneg hC).2 fun j => h τ i j

theorem norm_topL_le : ‖topL T r s p‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t => by
    rw [one_mul]
    exact norm_le_of_coord (norm_nonneg _) fun τ i j => norm_coord_le t τ _ j

theorem norm_botL_le : ‖botL T r s p‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t => by
    rw [one_mul]
    exact norm_le_of_coord (norm_nonneg _) fun τ i j => norm_coord_le t τ _ j

theorem norm_le_max (t : T → Fin (r + s) → Fin p → ℂ) : ‖t‖ ≤ max ‖topL T r s p t‖ ‖botL T r s p t‖ := by
  refine norm_le_of_coord (le_max_of_le_left (norm_nonneg _)) fun τ i j => ?_
  induction i using Fin.addCases with
  | left a => exact le_max_of_le_left (norm_coord_le (topL T r s p t) τ a j)
  | right b => exact le_max_of_le_right (norm_coord_le (botL T r s p t) τ b j)

end Coord

section Finite

variable {R : Type} {tR : TopologicalSpace R} {r s p : ℕ}

def joinR (a : Fin r → Fin p → R) (b : Fin s → Fin p → R) : Fin (r + s) → Fin p → R :=
  fun i j => Fin.addCases (motive := fun _ => R) (fun u => a u j) (fun v => b v j) i

theorem continuous_joinR :
    Continuous fun q : (Fin r → Fin p → R) × (Fin s → Fin p → R) => joinR q.1 q.2 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  induction i using Fin.addCases with
  | left a => simp only [joinR, Fin.addCases_left]; fun_prop
  | right b => simp only [joinR, Fin.addCases_right]; fun_prop

theorem sb_tensor {g : (Fin r → Fin p → R) → ℂ} {g' : (Fin s → Fin p → R) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin r → Fin p → R)) (hg' : g' ∈ GlobalTheory.WeilM.SB (Fin s → Fin p → R)) :
    (fun u : Fin (r + s) → Fin p → R =>
      g (fun i j => u (Fin.castAdd s i) j) * g' (fun i j => u (Fin.natAdd r i) j)) ∈
      GlobalTheory.WeilM.SB (Fin (r + s) → Fin p → R) := by
  obtain ⟨hl, hc⟩ := hg
  obtain ⟨hl', hc'⟩ := hg'
  have hT : Continuous fun u : Fin (r + s) → Fin p → R => fun (i : Fin r) (j : Fin p) => u (Fin.castAdd s i) j := by
    fun_prop
  have hB : Continuous fun u : Fin (r + s) → Fin p → R => fun (i : Fin s) (j : Fin p) => u (Fin.natAdd r i) j := by
    fun_prop
  have hlc := (hl.comp_continuous hT).mul (hl'.comp_continuous hB)
  refine ⟨hlc, ?_⟩
  set G : (Fin (r + s) → Fin p → R) → ℂ := fun u =>
    g (fun i j => u (Fin.castAdd s i) j) * g' (fun i j => u (Fin.natAdd r i) j) with hG
  have hlG : IsLocallyConstant G := hlc
  have hclosed : IsClosed (Function.support G) := by
    have : Function.support G = (G ⁻¹' {0})ᶜ := by ext u; simp [Function.mem_support]
    rw [this]
    exact (hlG.isOpen_fiber 0).isClosed_compl
  have hK : IsCompact ((fun q : (Fin r → Fin p → R) × (Fin s → Fin p → R) => joinR q.1 q.2) ''
      (tsupport g ×ˢ tsupport g')) := (IsCompact.prod hc hc').image continuous_joinR
  have hsub : Function.support G ⊆ (fun q : (Fin r → Fin p → R) × (Fin s → Fin p → R) => joinR q.1 q.2) ''
      (tsupport g ×ˢ tsupport g') := by
    intro u hu
    have hu' : G u ≠ 0 := hu
    refine ⟨(fun i j => u (Fin.castAdd s i) j, fun i j => u (Fin.natAdd r i) j), ⟨?_, ?_⟩, ?_⟩
    · exact subset_tsupport _ (left_ne_zero_of_mul hu')
    · exact subset_tsupport _ (right_ne_zero_of_mul hu')
    · funext i j
      induction i using Fin.addCases with
      | left a => simp [joinR]
      | right b => simp [joinR]
  have : HasCompactSupport G := by
    unfold HasCompactSupport tsupport
    rw [hclosed.closure_eq]
    exact hK.of_isClosed_subset hclosed hsub
  exact this

end Finite

theorem schwTensor : SchwTensor := by
  intro D θ _ r s p φ hφ φ' hφ'
  induction hφ using Submodule.span_induction with
  | zero =>
    convert (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).zero_mem using 1
    funext y; simp
  | add a b _ _ ha hb =>
    have := (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).add_mem ha hb
    convert this using 1
    funext y; simp [add_mul]
  | smul c a _ ha =>
    have := (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).smul_mem c ha
    convert this using 1
    funext y; simp [mul_assoc]
  | mem a ha =>
    obtain ⟨f, g, hg, rfl⟩ := ha
    induction hφ' using Submodule.span_induction with
    | zero =>
    convert (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).zero_mem using 1
    funext y; simp
    | add a b _ _ ha hb =>
      have := (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).add_mem ha hb
      convert this using 1
      funext y; simp [mul_add]
    | smul c a _ ha =>
      have := (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).smul_mem c ha
      convert this using 1
      funext y; simp only [Pi.smul_apply, smul_eq_mul]; ring
    | mem b hb =>
      obtain ⟨f', g', hg', rfl⟩ := hb
      refine Submodule.subset_span ⟨tens (topL _ r s p) (botL _ r s p) norm_topL_le norm_botL_le norm_le_max f f',
        _, sb_tensor hg hg', ?_⟩
      funext y
      simp only [tens_apply]
      exact mul_mul_mul_comm _ _ _ _

end GlobalTheory.CompanionTheory.ThTot.SchwT

end
