import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice

open MeasureTheory NumberField Topology Filter Set
open scoped NumberField.AdeleRing Classical nonZeroDivisors

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open GroundTheory.Global GJMatrix

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem locHeight_infAt_le_height (g : AdelicGLn.AdelicGL K n) (w : InfinitePlace K) :
    AutomorphicForm.locHeight (Reduction.infAt w g) ≤ AutomorphicForm.height g := by
  unfold AutomorphicForm.height
  have h1 : ∀ w' ∈ (Finset.univ : Finset (InfinitePlace K)),
      1 ≤ AutomorphicForm.locHeight (Reduction.infAt w' g) ^ w'.mult :=
    fun w' _ => one_le_pow₀ (AutomorphicForm.one_le_locHeight _)
  have hmult : w.mult ≠ 0 := by unfold InfinitePlace.mult; split_ifs <;> norm_num
  calc AutomorphicForm.locHeight (Reduction.infAt w g)
      ≤ AutomorphicForm.locHeight (Reduction.infAt w g) ^ w.mult :=
        le_self_pow₀ (AutomorphicForm.one_le_locHeight _) hmult
    _ ≤ ∏ w' : InfinitePlace K, AutomorphicForm.locHeight (Reduction.infAt w' g) ^ w'.mult := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
        exact le_mul_of_one_le_right (zero_le_one.trans (h1 w (Finset.mem_univ w)))
          (Finset.one_le_prod fun w' hw' => h1 w' (Finset.mem_of_mem_erase hw'))
    _ ≤ _ := le_mul_of_one_le_right (zero_le_one.trans (AutomorphicForm.one_le_prod_locHeight g))
          (AutomorphicForm.one_le_finprod_locHeight g)

theorem norm_apply_fst_le_height (g : AdelicGLn.AdelicGL K n) (i j : Fin n)
    (w : InfinitePlace K) :
    ‖((g : Matrix (Fin n) (Fin n) 𝔸[K]) i j).1 w‖ ≤ AutomorphicForm.height g := by
  rw [← Reduction.infAt_apply]
  exact (AutomorphicForm.norm_apply_le_locHeight _ i j).trans (locHeight_infAt_le_height g w)

theorem infNorm_le_height (g : AdelicGLn.AdelicGL K n) :
    infNorm (g : Matrix (Fin n) (Fin n) 𝔸[K]) ≤
      (n * n * Fintype.card (InfinitePlace K) : ℝ) * AutomorphicForm.height g := by
  calc infNorm (g : Matrix (Fin n) (Fin n) 𝔸[K])
      ≤ ∑ _i : Fin n, ∑ _j : Fin n, ∑ _w : InfinitePlace K, AutomorphicForm.height g :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun w _ =>
          norm_apply_fst_le_height g i j w
    _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring

theorem one_add_infNorm_le_height (g : AdelicGLn.AdelicGL K n) :
    1 + infNorm (g : Matrix (Fin n) (Fin n) 𝔸[K]) ≤
      (1 + n * n * Fintype.card (InfinitePlace K) : ℝ) * AutomorphicForm.height g := by
  have h1 := infNorm_le_height g
  have h2 := AutomorphicForm.one_le_height g
  nlinarith [show (0 : ℝ) ≤ n * n * Fintype.card (InfinitePlace K) by positivity]

theorem continuous_finMat_coe : Continuous fun g : AdelicGLn.AdelicGL K n =>
    finMat (g : Matrix (Fin n) (Fin n) 𝔸[K]) :=
  continuous_finMat.comp Units.continuous_val

theorem finMat_diagUnits_posIdele (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i) :
    finMat ((Reduction.diagUnits n fun i => Reduction.posIdele (K := K) (ρ i) (hρ i) :
      AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) = 1 := by
  rw [Reduction.coe_diagUnits]
  refine Matrix.ext fun i j => ?_
  rw [finMat_apply]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    refine RestrictedProduct.ext _ _ fun v => ?_
    exact Reduction.posIdele_finite (K := K) (ρ i) (hρ i) v
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    rfl

theorem finMat_coe_inv_of_finMat_eq_one {a : AdelicGLn.AdelicGL K n}
    (ha : finMat (a : Matrix (Fin n) (Fin n) 𝔸[K]) = 1) :
    finMat ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) = 1 := by
  have h : finMat (a : Matrix (Fin n) (Fin n) 𝔸[K]) *
      finMat ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) = 1 := by
    rw [← finMat_mul, Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rwa [ha, one_mul] at h

theorem exists_isCompact_finMat_siegelSet {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω)
    (t : ℝ) : ∃ Q : Set (Matrix (Fin n) (Fin n) 𝔸ᶠ[K]), IsCompact Q ∧
      ∀ x ∈ Reduction.siegelSet n ω t, finMat (x : Matrix (Fin n) (Fin n) 𝔸[K]) ∈ Q ∧
        finMat ((x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) ∈ Q := by
  set Kc : Set (AdelicGLn.AdelicGL K n) :=
    ((Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n))
  have hK : IsCompact Kc := Reduction.isCompact_maxCompact
  set f₁ : AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n → Matrix (Fin n) (Fin n) 𝔸ᶠ[K] :=
    fun p => finMat (p.1 : Matrix (Fin n) (Fin n) 𝔸[K]) * finMat (p.2 : Matrix (Fin n) (Fin n) 𝔸[K])
  set f₂ : AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n → Matrix (Fin n) (Fin n) 𝔸ᶠ[K] :=
    fun p => finMat ((p.2⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
      finMat ((p.1⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])
  have hc₁ : Continuous f₁ := (continuous_finMat_coe.comp continuous_fst).matrix_mul
    (continuous_finMat_coe.comp continuous_snd)
  have hc₂ : Continuous f₂ := (continuous_finMat_coe.comp (continuous_snd.inv)).matrix_mul
    (continuous_finMat_coe.comp (continuous_fst.inv))
  refine ⟨f₁ '' (ω ×ˢ Kc) ∪ f₂ '' (ω ×ˢ Kc), ((hω.prod hK).image hc₁).union ((hω.prod hK).image hc₂),
    fun x hx => ?_⟩
  obtain ⟨b, hb, a, ⟨r, hr, -, rfl⟩, k, hk, rfl⟩ := hx
  have ha := finMat_diagUnits_posIdele (K := K) r hr
  refine ⟨Or.inl ⟨(b, k), ⟨hb, hk⟩, ?_⟩, Or.inr ⟨(b, k), ⟨hb, hk⟩, ?_⟩⟩
  · simp only [f₁, Units.val_mul, finMat_mul, ha, Matrix.mul_one]
  · simp only [f₂, mul_inv_rev, Units.val_mul, finMat_mul, finMat_coe_inv_of_finMat_eq_one ha,
      Matrix.one_mul]

theorem exists_tsum_norm_le_siegel {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω)
    (t₀ : ℝ) {M : ℕ} (hM : Module.finrank ℝ (Fin n × Fin n → mixedEmbedding.mixedSpace K) < M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Reduction.siegelSet n ω t₀, ∀ y ∈ Reduction.siegelSet n ω t₀,
      ∀ t : {r : ℝ // 0 < r},
      Summable (fun ξ : Matrix (Fin n) (Fin n) K => ‖Φ (((Reduction.centralSection K n t * x⁻¹ :
        AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          (y : Matrix (Fin n) (Fin n) 𝔸[K]))‖) ∧
      ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Φ (((Reduction.centralSection K n t * x⁻¹ :
        AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          (y : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤
        C * (max 1 (centralScale (K := K) n t)⁻¹) ^ M *
          (AutomorphicForm.height x * AutomorphicForm.height y) ^ M := by
  obtain ⟨C₁, hC₁, I, hmaj⟩ := exists_majorant hΦ M
  obtain ⟨Q, hQ, hQmem⟩ := exists_isCompact_finMat_siegelSet (K := K) (n := n) hω t₀
  obtain ⟨S, hS0, hS⟩ := exists_tsum_twistedWeight_le hQ I hM
  set c : ℝ := 1 + n * n * Fintype.card (InfinitePlace K) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨C₁ * c ^ (2 * M) * S, by positivity, fun x hx y hy t => ?_⟩
  obtain ⟨hsum, hle⟩ := hS x y (hQmem x hx).1 (hQmem y hy).2
  have hpt := norm_le_twistedWeight hC₁ hmaj t x y
  set m := (max 1 (centralScale (K := K) n t)⁻¹) ^ M with hm
  have hm0 : 0 ≤ m := pow_nonneg (zero_le_one.trans (le_max_left _ _)) M
  have hs' := hsum.mul_left (C₁ * m)
  have hsum' : Summable (fun ξ : Matrix (Fin n) (Fin n) K => ‖Φ (((Reduction.centralSection K n t *
      x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
        (y : Matrix (Fin n) (Fin n) 𝔸[K]))‖) :=
    hs'.of_nonneg_of_le (fun _ => norm_nonneg _) hpt
  refine ⟨hsum', ?_⟩
  have hx1 := one_add_infNorm_le_height (K := K) x
  have hy1 := one_add_infNorm_le_height (K := K) (y⁻¹)
  rw [AutomorphicForm.height_inv] at hy1
  have hxh := AutomorphicForm.one_le_height x
  have hyh := AutomorphicForm.one_le_height y
  have h0x : 0 ≤ 1 + infNorm (x : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    linarith [infNorm_nonneg (x : Matrix (Fin n) (Fin n) 𝔸[K])]
  have h0y : 0 ≤ 1 + infNorm ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    linarith [infNorm_nonneg ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])]
  calc ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Φ (((Reduction.centralSection K n t * x⁻¹ :
        AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          (y : Matrix (Fin n) (Fin n) 𝔸[K]))‖
      ≤ ∑' ξ, C₁ * m * twistedWeight I M x y ξ := hsum'.tsum_le_tsum hpt hs'
    _ = C₁ * m * ∑' ξ, twistedWeight I M x y ξ := tsum_mul_left
    _ ≤ C₁ * m * (((1 + infNorm (x : Matrix (Fin n) (Fin n) 𝔸[K])) *
        (1 + infNorm ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))) ^ M * S) :=
        mul_le_mul_of_nonneg_left hle (mul_nonneg hC₁ hm0)
    _ ≤ C₁ * m * ((c * AutomorphicForm.height x * (c * AutomorphicForm.height y)) ^ M * S) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_left₀
          (mul_nonneg h0x h0y) (mul_le_mul hx1 hy1 h0y (by positivity)) M) hS0)
          (mul_nonneg hC₁ hm0)
    _ = C₁ * c ^ (2 * M) * S * m *
          (AutomorphicForm.height x * AutomorphicForm.height y) ^ M := by
        rw [show c * AutomorphicForm.height x * (c * AutomorphicForm.height y) =
          c ^ 2 * (AutomorphicForm.height x * AutomorphicForm.height y) by ring, mul_pow,
          ← pow_mul]
        ring

theorem coe_mul_ratMat_mul_reindex (t : {r : ℝ // 0 < r}) (x y : AdelicGLn.AdelicGL K n)
    (γ₁ γ₂ : GL (Fin n) K) (ξ : Matrix (Fin n) (Fin n) K) :
    ((Reduction.centralSection K n t * (AdelicGLn.diagonal K n γ₁ * x)⁻¹ :
        AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
        ((AdelicGLn.diagonal K n γ₂ * y : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      ((Reduction.centralSection K n t * x⁻¹ : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat (((γ₁⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ξ *
          (γ₂ : Matrix (Fin n) (Fin n) K)) * (y : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  rw [mul_inv_rev, ← map_inv]
  simp only [Units.val_mul, coe_diagonal, ratMat_mul, Matrix.mul_assoc]

def reindexEquiv (γ₁ γ₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K ≃ Matrix (Fin n) (Fin n) K where
  toFun ξ := ((γ₁⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ξ * (γ₂ : Matrix (Fin n) (Fin n) K)
  invFun ξ := (γ₁ : Matrix (Fin n) (Fin n) K) * ξ * ((γ₂⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  left_inv ξ := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Units.mul_inv_cancel_left]
  right_inv ξ := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Units.inv_mul_cancel_left]

theorem summable_tsum_reindex (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) (t : {r : ℝ // 0 < r})
    (x y : AdelicGLn.AdelicGL K n) (γ₁ γ₂ : GL (Fin n) K) :
    (Summable (fun ξ : Matrix (Fin n) (Fin n) K => ‖Φ (((Reduction.centralSection K n t *
        (AdelicGLn.diagonal K n γ₁ * x)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
          ratMat ξ * ((AdelicGLn.diagonal K n γ₂ * y : AdelicGLn.AdelicGL K n) :
            Matrix (Fin n) (Fin n) 𝔸[K]))‖) ↔
      Summable (fun ξ : Matrix (Fin n) (Fin n) K => ‖Φ (((Reduction.centralSection K n t * x⁻¹ :
        AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          (y : Matrix (Fin n) (Fin n) 𝔸[K]))‖)) ∧
    ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Φ (((Reduction.centralSection K n t *
        (AdelicGLn.diagonal K n γ₁ * x)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
          ratMat ξ * ((AdelicGLn.diagonal K n γ₂ * y : AdelicGLn.AdelicGL K n) :
            Matrix (Fin n) (Fin n) 𝔸[K]))‖ =
      ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Φ (((Reduction.centralSection K n t * x⁻¹ :
        AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          (y : Matrix (Fin n) (Fin n) 𝔸[K]))‖ := by
  set f : Matrix (Fin n) (Fin n) K → ℝ := fun ξ => ‖Φ (((Reduction.centralSection K n t * x⁻¹ :
    AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
      (y : Matrix (Fin n) (Fin n) 𝔸[K]))‖ with hf
  have h : (fun ξ : Matrix (Fin n) (Fin n) K => ‖Φ (((Reduction.centralSection K n t *
      (AdelicGLn.diagonal K n γ₁ * x)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat ξ * ((AdelicGLn.diagonal K n γ₂ * y : AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) 𝔸[K]))‖) = f ∘ reindexEquiv γ₁ γ₂ := by
    funext ξ
    simp only [Function.comp_apply, hf, coe_mul_ratMat_mul_reindex]
    rfl
  rw [h]
  exact ⟨(reindexEquiv γ₁ γ₂).summable_iff, (reindexEquiv γ₁ γ₂).tsum_eq f⟩

theorem exists_norm_le_of_mem_siegelSet {ψ : AdelicGLn.AdelicGL K n → ℂ}
    (hψ : ψ ∈ AutomorphicForm.cuspForms K n) {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω)
    (hωB : ω ⊆ ((Reduction.adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) :
      Set (AdelicGLn.AdelicGL K n))) {t₀ : ℝ} (ht₀ : 0 < t₀) (N : ℕ) :
    ∃ C : ℝ, ∀ x ∈ Reduction.siegelSet n ω t₀, x ∈ Reduction.normOneGL K n →
      ‖ψ x‖ ≤ C * (AutomorphicForm.height x ^ N)⁻¹ := by
  obtain ⟨C, hC⟩ := CuspidalSpectrum.exists_norm_le_height_pow_neg_siegel hψ hω hωB ht₀ N
  refine ⟨C, fun x hx hx1 => ?_⟩
  obtain ⟨b, hb, a, ⟨r, hr, hcond, rfl⟩, k, hk, rfl⟩ := hx
  exact hC b hb r hr hcond k hk _ hx1 rfl

theorem max_one_centralScale_inv_pow (t : {r : ℝ // 0 < r}) (M : ℕ) :
    (max 1 (centralScale (K := K) n t)⁻¹) ^ M =
      (max 1 (t : ℝ)⁻¹) ^ ((M : ℝ) * ((n * Module.finrank ℚ K : ℝ))⁻¹) := by
  set e : ℝ := ((n * Module.finrank ℚ K : ℝ))⁻¹ with he
  have he0 : 0 ≤ e := inv_nonneg.2 (by positivity)
  have ht0 : (0 : ℝ) ≤ (t : ℝ)⁻¹ := inv_nonneg.2 t.2.le
  have h1 : (centralScale (K := K) n t)⁻¹ = ((t : ℝ)⁻¹) ^ e := by
    rw [centralScale, Real.inv_rpow t.2.le]
  have h2 : max 1 (((t : ℝ)⁻¹) ^ e) = (max 1 (t : ℝ)⁻¹) ^ e := by
    by_cases h : 1 ≤ (t : ℝ)⁻¹
    · rw [max_eq_right h, max_eq_right (Real.one_le_rpow h he0)]
    · push Not at h
      rw [max_eq_left h.le, Real.one_rpow, max_eq_left (Real.rpow_le_one ht0 h.le he0)]
  rw [h1, h2, ← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans (le_max_left _ _)), mul_comm]

theorem exists_bound_tsum {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) {ψ₁ ψ₂ : AdelicGLn.AdelicGL K n → ℂ}
    (h₁ : ψ₁ ∈ AutomorphicForm.cuspForms K n) (h₂ : ψ₂ ∈ AutomorphicForm.cuspForms K n) :
    ∃ C M : ℝ, 0 ≤ C ∧ ∀ x ∈ Reduction.normOneGL K n, ∀ y ∈ Reduction.normOneGL K n,
      ∀ t : {r : ℝ // 0 < r},
      Summable (fun ξ : Matrix (Fin n) (Fin n) K => ‖Φ (((Reduction.centralSection K n t * x⁻¹ :
        AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          (y : Matrix (Fin n) (Fin n) 𝔸[K]))‖) ∧
      ‖ψ₂ x‖ * ‖ψ₁ y‖ * ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Φ (((Reduction.centralSection K n t *
        x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          (y : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤ C * (max 1 (t : ℝ)⁻¹) ^ M := by
  obtain ⟨ω, hω, hωB, t₀, ht₀, hsieg⟩ := Reduction.exists_siegelSet (K := K) n
  set M : ℕ := Module.finrank ℝ (Fin n × Fin n → mixedEmbedding.mixedSpace K) + 1 with hM
  obtain ⟨C, hC, hbound⟩ := exists_tsum_norm_le_siegel hΦ hω t₀ (M := M) (by omega)
  obtain ⟨C₁, hC₁⟩ := exists_norm_le_of_mem_siegelSet h₁ hω hωB ht₀ M
  obtain ⟨C₂, hC₂⟩ := exists_norm_le_of_mem_siegelSet h₂ hω hωB ht₀ M
  refine ⟨max C₂ 0 * max C₁ 0 * C, (M : ℝ) * ((n * Module.finrank ℚ K : ℝ))⁻¹, by positivity,
    fun x hx y hy t => ?_⟩
  obtain ⟨γ₁, hγ₁⟩ := hsieg x
  obtain ⟨γ₂, hγ₂⟩ := hsieg y
  have hγ₁1 : AdelicGLn.diagonal K n γ₁ * x ∈ Reduction.normOneGL K n :=
    mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ₁, rfl⟩) hx
  have hγ₂1 : AdelicGLn.diagonal K n γ₂ * y ∈ Reduction.normOneGL K n :=
    mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ₂, rfl⟩) hy
  obtain ⟨hsum, hle⟩ := hbound _ hγ₁ _ hγ₂ t
  obtain ⟨hiff, heq⟩ := summable_tsum_reindex Φ t x y γ₁ γ₂
  refine ⟨hiff.1 hsum, ?_⟩
  rw [← heq, ← h₂.1.isLeftInvariant γ₁ x, ← h₁.1.isLeftInvariant γ₂ y,
    ← max_one_centralScale_inv_pow]
  set x' := AdelicGLn.diagonal K n γ₁ * x
  set y' := AdelicGLn.diagonal K n γ₂ * y
  have hx' := hC₂ x' hγ₁ hγ₁1
  have hy' := hC₁ y' hγ₂ hγ₂1
  have hhx := AutomorphicForm.height_pos x'
  have hhy := AutomorphicForm.height_pos y'
  set m := (max 1 (centralScale (K := K) n t)⁻¹) ^ M
  have hm0 : 0 ≤ m := pow_nonneg (zero_le_one.trans (le_max_left _ _)) M
  set T := ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Φ (((Reduction.centralSection K n t * x'⁻¹ :
    AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
      (y' : Matrix (Fin n) (Fin n) 𝔸[K]))‖
  have hT0 : 0 ≤ T := tsum_nonneg fun _ => norm_nonneg _
  have hpx : ‖ψ₂ x'‖ ≤ max C₂ 0 * (AutomorphicForm.height x' ^ M)⁻¹ :=
    hx'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.2 (pow_nonneg hhx.le _)))
  have hpy : ‖ψ₁ y'‖ ≤ max C₁ 0 * (AutomorphicForm.height y' ^ M)⁻¹ :=
    hy'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.2 (pow_nonneg hhy.le _)))
  calc ‖ψ₂ x'‖ * ‖ψ₁ y'‖ * T
      ≤ (max C₂ 0 * (AutomorphicForm.height x' ^ M)⁻¹) *
          (max C₁ 0 * (AutomorphicForm.height y' ^ M)⁻¹) *
          (C * m * (AutomorphicForm.height x' * AutomorphicForm.height y') ^ M) :=
        mul_le_mul (mul_le_mul hpx hpy (norm_nonneg _) (by positivity)) hle hT0 (by positivity)
    _ = max C₂ 0 * max C₁ 0 * C * m := by
        rw [mul_pow]
        field_simp

theorem exists_bound_tsum_one {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) {ψ : AdelicGLn.AdelicGL K n → ℂ}
    (hψ : ψ ∈ AutomorphicForm.cuspForms K n) (y : AdelicGLn.AdelicGL K n) :
    ∃ C : ℝ, ∀ g ∈ Reduction.normOneGL K n,
      Summable (fun ξ : Matrix (Fin n) (Fin n) K => ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖) ∧
      ‖ψ g‖ * ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤ C := by
  obtain ⟨ω, hω, hωB, t₀, ht₀, hsieg⟩ := Reduction.exists_siegelSet (K := K) n
  set M : ℕ := Module.finrank ℝ (Fin n × Fin n → mixedEmbedding.mixedSpace K) + 1 with hM
  obtain ⟨C, hC, hbound⟩ := exists_tsum_norm_le_siegel hΦ hω t₀ (M := M) (by omega)
  obtain ⟨C₁, hC₁⟩ := exists_norm_le_of_mem_siegelSet hψ hω hωB ht₀ M
  obtain ⟨s, y₁, -, rfl⟩ := CuspidalSpectrum.exists_centralSection_mul_mem_normOneGL y
  obtain ⟨γ₁, hγ₁⟩ := hsieg y₁⁻¹
  set x' := AdelicGLn.diagonal K n γ₁ * y₁⁻¹
  set m := (max 1 (centralScale (K := K) n s)⁻¹) ^ M
  have hm0 : 0 ≤ m := pow_nonneg (zero_le_one.trans (le_max_left _ _)) M
  refine ⟨max C₁ 0 * C * m * AutomorphicForm.height x' ^ M, fun g hg => ?_⟩
  obtain ⟨γ₂, hγ₂⟩ := hsieg g
  have hγ₂1 : AdelicGLn.diagonal K n γ₂ * g ∈ Reduction.normOneGL K n :=
    mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ₂, rfl⟩) hg
  have hy : Reduction.centralSection K n s * y₁ = Reduction.centralSection K n s * (y₁⁻¹)⁻¹ := by
    rw [inv_inv]
  rw [hy]
  obtain ⟨hsum, hle⟩ := hbound _ hγ₁ _ hγ₂ s
  obtain ⟨hiff, heq⟩ := summable_tsum_reindex Φ s y₁⁻¹ g γ₁ γ₂
  refine ⟨hiff.1 hsum, ?_⟩
  rw [← heq, ← hψ.1.isLeftInvariant γ₂ g]
  set g' := AdelicGLn.diagonal K n γ₂ * g
  have hg' := hC₁ g' hγ₂ hγ₂1
  have hhg := AutomorphicForm.height_pos g'
  have hhx := AutomorphicForm.height_pos x'
  have hpg : ‖ψ g'‖ ≤ max C₁ 0 * (AutomorphicForm.height g' ^ M)⁻¹ :=
    hg'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.2 (pow_nonneg hhg.le _)))
  calc ‖ψ g'‖ * ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Φ (((Reduction.centralSection K n s * x'⁻¹ :
        AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          (g' : Matrix (Fin n) (Fin n) 𝔸[K]))‖
      ≤ (max C₁ 0 * (AutomorphicForm.height g' ^ M)⁻¹) *
          (C * m * (AutomorphicForm.height x' * AutomorphicForm.height g') ^ M) :=
        mul_le_mul hpg hle (tsum_nonneg fun _ => norm_nonneg _) (by positivity)
    _ = max C₁ 0 * C * m * AutomorphicForm.height x' ^ M := by
        rw [mul_pow]
        field_simp

def reindexGL (γ₁ γ₂ : GL (Fin n) K) : GL (Fin n) K ≃ GL (Fin n) K :=
  (Equiv.mulLeft γ₁⁻¹).trans (Equiv.mulRight γ₂)

theorem centralSection_mul_reindex (t : {r : ℝ // 0 < r}) (x y : AdelicGLn.AdelicGL K n)
    (γ₁ γ₂ γ : GL (Fin n) K) :
    Reduction.centralSection K n t * (AdelicGLn.diagonal K n γ₁ * x)⁻¹ * AdelicGLn.diagonal K n γ *
        (AdelicGLn.diagonal K n γ₂ * y) =
      Reduction.centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n (reindexGL γ₁ γ₂ γ) * y := by
  simp only [reindexGL, Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight, map_mul, map_inv,
    mul_inv_rev, mul_assoc]

theorem exists_decay_siegel (hn : 0 < n) {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω)
    (t₀ : ℝ) {M : ℕ} (hM : Module.finrank ℝ (Fin n × Fin n → mixedEmbedding.mixedSpace K) < M)
    (N : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Reduction.siegelSet n ω t₀, x ∈ Reduction.normOneGL K n →
      ∀ y ∈ Reduction.siegelSet n ω t₀, y ∈ Reduction.normOneGL K n →
      ∀ t : {r : ℝ // 0 < r}, 1 ≤ (t : ℝ) →
      Summable (fun γ : GL (Fin n) K => ‖Φ ((Reduction.centralSection K n t * x⁻¹ *
        AdelicGLn.diagonal K n γ * y : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])‖) ∧
      ∑' γ : GL (Fin n) K, ‖Φ ((Reduction.centralSection K n t * x⁻¹ *
        AdelicGLn.diagonal K n γ * y : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])‖ ≤
        C * (t : ℝ) ^ (-N) * (AutomorphicForm.height x * AutomorphicForm.height y) ^ M := by
  set d := Module.finrank ℚ K with hd
  have hd1 : 1 ≤ d := Module.finrank_pos
  set M' : ℕ := ⌈N * (n * d)⌉₊ with hM'
  obtain ⟨C₁, hC₁, I, hmaj⟩ := exists_majorant hΦ (M + M')
  obtain ⟨c₀, hc₀, hc₀le⟩ := exists_le_infNorm_of_isInBox (K := K) hn I
  obtain ⟨Q, hQ, hQmem⟩ := exists_isCompact_finMat_siegelSet (K := K) (n := n) hω t₀
  obtain ⟨S, hS0, hS⟩ := exists_tsum_twistedWeight_le hQ I hM
  set c : ℝ := 1 + n * n * Fintype.card (InfinitePlace K) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨C₁ * (c₀ ^ M')⁻¹ * c ^ (2 * M) * S, by positivity,
    fun x hx hx1 y hy hy1 t ht => ?_⟩
  obtain ⟨hsum, hle⟩ := hS x y (hQmem x hx).1 (hQmem y hy).2
  obtain ⟨a, ha1, ha2, hmul⟩ := exists_centralSection_mul_eq (K := K) (n := n) t
  set ρ := centralScale (K := K) n t with hρ
  have hρ1 : 1 ≤ ρ := Real.one_le_rpow ht (inv_nonneg.2 (by positivity))

  have hpt : ∀ γ : GL (Fin n) K, ‖Φ ((Reduction.centralSection K n t * x⁻¹ *
      AdelicGLn.diagonal K n γ * y : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])‖ ≤
      C₁ * ((ρ * c₀) ^ M')⁻¹ * twistedWeight I M x y (γ : Matrix (Fin n) (Fin n) K) := by
    intro γ
    set W := ((x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
      ratMat (γ : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) 𝔸[K]) with hW
    have heq : ((Reduction.centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y :
        AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) = a • W := by
      rw [hW, ← hmul]
      simp only [Units.val_mul, coe_diagonal, Matrix.mul_assoc]
    have hWG : ((x⁻¹ * AdelicGLn.diagonal K n γ * y : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) = W := by
      rw [hW]
      simp only [Units.val_mul, coe_diagonal]
    rw [heq]
    refine (hmaj _).trans ?_
    rw [infNorm_smul ha1, isInBox_smul_iff ha2]
    unfold twistedWeight
    rw [← hW]
    by_cases hbox : IsInBox I W
    · rw [if_pos hbox, mul_one, mul_one]
      have hdet : (Reduction.detModule K n (x⁻¹ * AdelicGLn.diagonal K n γ * y) : ℝ) = 1 := by
        have hmem : x⁻¹ * AdelicGLn.diagonal K n γ * y ∈ Reduction.normOneGL K n :=
          mul_mem (mul_mem (inv_mem hx1) (Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩)) hy1
        rw [Reduction.mem_normOneGL_iff_detModule.1 hmem]
        rfl
      have hw := hc₀le _ hdet (by rw [hWG]; exact hbox)
      rw [hWG] at hw
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (inv_one_add_mul_pow_add_le hρ1 hc₀ hw M M') hC₁
    · simp only [if_neg hbox, mul_zero, le_refl]
  have hsumγ : Summable fun γ : GL (Fin n) K =>
      twistedWeight I M x y (γ : Matrix (Fin n) (Fin n) K) :=
    hsum.comp_injective (fun _ _ h => Units.ext h)
  have hs' := hsumγ.mul_left (C₁ * ((ρ * c₀) ^ M')⁻¹)
  have hsum' := hs'.of_nonneg_of_le (fun _ => norm_nonneg _) hpt
  refine ⟨hsum', ?_⟩
  have hρN : ((ρ * c₀) ^ M')⁻¹ ≤ (c₀ ^ M')⁻¹ * (t : ℝ) ^ (-N) := by
    rw [mul_pow, mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (pow_nonneg hc₀.le _))
    rw [Real.rpow_neg t.2.le]
    refine inv_anti₀ (Real.rpow_pos_of_pos t.2 _) ?_
    rw [hρ, centralScale, ← Real.rpow_natCast, ← Real.rpow_mul t.2.le]
    refine Real.rpow_le_rpow_of_exponent_le ht ?_
    have hnd : (0 : ℝ) < n * d := by positivity
    rw [inv_mul_eq_div, le_div_iff₀ hnd]
    exact Nat.le_ceil _
  have hx1' := one_add_infNorm_le_height (K := K) x
  have hy1' := one_add_infNorm_le_height (K := K) (y⁻¹)
  rw [AutomorphicForm.height_inv] at hy1'
  have h0x : 0 ≤ 1 + infNorm (x : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    linarith [infNorm_nonneg (x : Matrix (Fin n) (Fin n) 𝔸[K])]
  have h0y : 0 ≤ 1 + infNorm ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    linarith [infNorm_nonneg ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])]
  have hxh := AutomorphicForm.one_le_height x
  have hyh := AutomorphicForm.one_le_height y
  have hρc : 0 < ρ * c₀ := mul_pos (zero_lt_one.trans_le hρ1) hc₀
  calc ∑' γ : GL (Fin n) K, ‖Φ ((Reduction.centralSection K n t * x⁻¹ *
        AdelicGLn.diagonal K n γ * y : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])‖
      ≤ ∑' γ : GL (Fin n) K, C₁ * ((ρ * c₀) ^ M')⁻¹ *
          twistedWeight I M x y (γ : Matrix (Fin n) (Fin n) K) := hsum'.tsum_le_tsum hpt hs'
    _ = C₁ * ((ρ * c₀) ^ M')⁻¹ * ∑' γ : GL (Fin n) K,
          twistedWeight I M x y (γ : Matrix (Fin n) (Fin n) K) := tsum_mul_left
    _ ≤ C₁ * ((ρ * c₀) ^ M')⁻¹ * ∑' ξ, twistedWeight I M x y ξ :=
        mul_le_mul_of_nonneg_left (hsumγ.tsum_le_tsum_of_inj
          (fun γ : GL (Fin n) K => (γ : Matrix (Fin n) (Fin n) K)) (fun _ _ h => Units.ext h)
          (fun c _ => twistedWeight_nonneg I M x y c) (fun _ => le_rfl) hsum) (by positivity)
    _ ≤ C₁ * ((c₀ ^ M')⁻¹ * (t : ℝ) ^ (-N)) * (((1 + infNorm (x : Matrix (Fin n) (Fin n) 𝔸[K])) *
        (1 + infNorm ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))) ^ M * S) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hρN hC₁) hle
          (tsum_nonneg (twistedWeight_nonneg I M x y)) (by positivity)
    _ ≤ C₁ * ((c₀ ^ M')⁻¹ * (t : ℝ) ^ (-N)) *
          ((c * AutomorphicForm.height x * (c * AutomorphicForm.height y)) ^ M * S) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_left₀
          (mul_nonneg h0x h0y) (mul_le_mul hx1' hy1' h0y (by positivity)) M) hS0)
          (by positivity)
    _ = C₁ * (c₀ ^ M')⁻¹ * c ^ (2 * M) * S * (t : ℝ) ^ (-N) *
          (AutomorphicForm.height x * AutomorphicForm.height y) ^ M := by
        rw [show c * AutomorphicForm.height x * (c * AutomorphicForm.height y) =
          c ^ 2 * (AutomorphicForm.height x * AutomorphicForm.height y) by ring, mul_pow,
          ← pow_mul]
        ring

theorem exists_decay_tsum (hn : 0 < n) {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) {ψ₁ ψ₂ : AdelicGLn.AdelicGL K n → ℂ}
    (h₁ : ψ₁ ∈ AutomorphicForm.cuspForms K n) (h₂ : ψ₂ ∈ AutomorphicForm.cuspForms K n) (N : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Reduction.normOneGL K n, ∀ y ∈ Reduction.normOneGL K n,
      ∀ t : {r : ℝ // 0 < r}, 1 ≤ (t : ℝ) →
      Summable (fun γ : GL (Fin n) K => ‖Φ ((Reduction.centralSection K n t * x⁻¹ *
        AdelicGLn.diagonal K n γ * y : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])‖) ∧
      ‖ψ₂ x‖ * ‖ψ₁ y‖ * ∑' γ : GL (Fin n) K, ‖Φ ((Reduction.centralSection K n t * x⁻¹ *
        AdelicGLn.diagonal K n γ * y : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])‖ ≤
        C * (t : ℝ) ^ (-N) := by
  obtain ⟨ω, hω, hωB, t₀, ht₀, hsieg⟩ := Reduction.exists_siegelSet (K := K) n
  set M : ℕ := Module.finrank ℝ (Fin n × Fin n → mixedEmbedding.mixedSpace K) + 1 with hM
  obtain ⟨C, hC, hbound⟩ := exists_decay_siegel hn hΦ hω t₀ (M := M) (by omega) N
  obtain ⟨C₁, hC₁⟩ := exists_norm_le_of_mem_siegelSet h₁ hω hωB ht₀ M
  obtain ⟨C₂, hC₂⟩ := exists_norm_le_of_mem_siegelSet h₂ hω hωB ht₀ M
  refine ⟨max C₂ 0 * max C₁ 0 * C, by positivity, fun x hx y hy t ht => ?_⟩
  obtain ⟨γ₁, hγ₁⟩ := hsieg x
  obtain ⟨γ₂, hγ₂⟩ := hsieg y
  have hγ₁1 : AdelicGLn.diagonal K n γ₁ * x ∈ Reduction.normOneGL K n :=
    mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ₁, rfl⟩) hx
  have hγ₂1 : AdelicGLn.diagonal K n γ₂ * y ∈ Reduction.normOneGL K n :=
    mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ₂, rfl⟩) hy
  obtain ⟨hsum, hle⟩ := hbound _ hγ₁ hγ₁1 _ hγ₂ hγ₂1 t ht
  set f : GL (Fin n) K → ℝ := fun γ => ‖Φ ((Reduction.centralSection K n t * x⁻¹ *
    AdelicGLn.diagonal K n γ * y : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])‖ with hf
  have hre : (fun γ : GL (Fin n) K => ‖Φ ((Reduction.centralSection K n t *
      (AdelicGLn.diagonal K n γ₁ * x)⁻¹ * AdelicGLn.diagonal K n γ *
        (AdelicGLn.diagonal K n γ₂ * y) : AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) 𝔸[K])‖) = f ∘ reindexGL γ₁ γ₂ := by
    funext γ
    simp only [Function.comp_apply, hf, centralSection_mul_reindex]
  rw [hre] at hsum hle
  refine ⟨(reindexGL γ₁ γ₂).summable_iff.1 hsum, ?_⟩
  have hteq : tsum (f ∘ ⇑(reindexGL γ₁ γ₂)) = tsum f := (reindexGL γ₁ γ₂).tsum_eq f
  rw [hteq] at hle
  rw [← h₂.1.isLeftInvariant γ₁ x, ← h₁.1.isLeftInvariant γ₂ y]
  set x' := AdelicGLn.diagonal K n γ₁ * x
  set y' := AdelicGLn.diagonal K n γ₂ * y
  have hx' := hC₂ x' hγ₁ hγ₁1
  have hy' := hC₁ y' hγ₂ hγ₂1
  have hhx := AutomorphicForm.height_pos x'
  have hhy := AutomorphicForm.height_pos y'
  have htN : 0 ≤ (t : ℝ) ^ (-N) := (Real.rpow_pos_of_pos t.2 _).le
  have hpx : ‖ψ₂ x'‖ ≤ max C₂ 0 * (AutomorphicForm.height x' ^ M)⁻¹ :=
    hx'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.2 (pow_nonneg hhx.le _)))
  have hpy : ‖ψ₁ y'‖ ≤ max C₁ 0 * (AutomorphicForm.height y' ^ M)⁻¹ :=
    hy'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.2 (pow_nonneg hhy.le _)))
  calc ‖ψ₂ x'‖ * ‖ψ₁ y'‖ * ∑' γ, f γ
      ≤ (max C₂ 0 * (AutomorphicForm.height x' ^ M)⁻¹) *
          (max C₁ 0 * (AutomorphicForm.height y' ^ M)⁻¹) *
          (C * (t : ℝ) ^ (-N) * (AutomorphicForm.height x' * AutomorphicForm.height y') ^ M) :=
        mul_le_mul (mul_le_mul hpx hpy (norm_nonneg _) (by positivity)) hle
          (tsum_nonneg fun _ => norm_nonneg _) (by positivity)
    _ = max C₂ 0 * max C₁ 0 * C * (t : ℝ) ^ (-N) := by
        rw [mul_pow]
        field_simp

end GJGlobal

end

end GroundTheory.Automorphic
