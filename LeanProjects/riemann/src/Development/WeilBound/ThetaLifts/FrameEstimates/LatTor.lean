import Development.WeilBound.ThetaLifts.FrameEstimates.IntMvPolynomialCoeffAbsSumMulLe

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sum_pos_lam {n d q y : ℕ} {lam : Fin n → (Fin q → ℝ) →ₗ[ℝ] ℝ} {ix iy : Fin q ↪ Fin n} (h1 : ∀ i j, ix i ≠ iy j)
    (h2 : ∀ i t, lam (ix i) t = t i ∧ lam (iy i) t = -t i) (h3 : ∀ k, (∀ i, ix i ≠ k ∧ iy i ≠ k) → lam k = 0)
    {lam' : Fin d → (Fin y → ℝ) →ₗ[ℝ] ℝ} {jx jy : Fin y ↪ Fin d} (h1' : ∀ i j, jx i ≠ jy j)
    (h2' : ∀ i t, lam' (jx i) t = t i ∧ lam' (jy i) t = -t i) (h3' : ∀ k, (∀ i, jx i ≠ k ∧ jy i ≠ k) → lam' k = 0)
    {s : Fin q → ℝ} {t : Fin y → ℝ} (hs : s ∈ Cone q) (ht : t ∈ Cone y) :
    ∑ k, ∑ l, max 0 (lam k s + lam' l t) = posWt n d s t := by
  let G : ℝ → ℝ := fun u => ∑ l, max 0 (u + lam' l t)
  have hG : ∀ u, G u = ∑ j, max 0 (u + t j) + ∑ j, max 0 (u + -t j) + ((d : ℝ) - 2 * y) * max 0 (u + 0) := fun u =>
    sum_lam h1' h2' h3' (fun v => max 0 (u + v)) t
  have h0 : G 0 = ∑ j, t j := by
    rw [hG]
    have a : ∀ j, max 0 (0 + t j) = t j := fun j => by rw [zero_add, max_eq_right (ht.2 j)]
    have b : ∀ j, max 0 (0 + -t j) = 0 := fun j => by rw [zero_add, max_eq_left (by linarith [ht.2 j])]
    simp only [a, b]
    simp
  have hs' : ∀ i, G (s i) + G (-s i) = ∑ j, 2 * max (s i) (t j) + ((d : ℝ) - 2 * y) * s i := by
    intro i
    have a : ∀ j, 2 * max (s i) (t j) =
        max 0 (s i + t j) + max 0 (s i + -t j) + (max 0 (-s i + t j) + max 0 (-s i + -t j)) := by
      intro j
      have := hs.2 i
      have := ht.2 j
      simp only [max_def]
      split_ifs <;> linarith
    rw [hG, hG, add_zero, add_zero, max_eq_right (hs.2 i), max_eq_left (by linarith [hs.2 i] : -s i ≤ 0)]
    simp only [a, Finset.sum_add_distrib]
    ring
  have := sum_lam h1 h2 h3 G s
  rw [← Finset.sum_add_distrib, h0] at this
  simp only [hs', Finset.sum_add_distrib, ← Finset.mul_sum] at this
  refine this.trans ?_
  simp only [posWt, ← Finset.mul_sum]

theorem tsum_fin_prod {α : Type} (q : ℕ) (φ : Fin q → α → ℝ≥0∞) :
    ∑' x : Fin q → α, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← (Fin.consEquiv fun _ : Fin (q + 1) => α).tsum_eq, ENNReal.tsum_prod', Fin.prod_univ_succ, ← ih,
      ← ENNReal.tsum_mul_right]
    refine tsum_congr fun a => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun x => ?_
    rw [Fin.prod_univ_succ]
    rfl

theorem tsum_fun_prod {ι α : Type} [Fintype ι] (φ : ι → α → ℝ≥0∞) :
    ∑' x : ι → α, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y := by
  let e := (Fintype.equivFin ι).symm
  rw [← e.prod_comp, ← tsum_fin_prod, ← (e.arrowCongr (Equiv.refl α)).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [← e.prod_comp]
  simp

def oneMaj (τ : ∀ w : InfinitePlace F, EmbOver E w) (m N : ℕ) (ν : ℝ) : E → ℝ≥0∞ :=
  Set.indicator {x | IsIntegral ℤ ((m : E) * x)} fun x =>
    ENNReal.ofReal (((1 + Real.exp (-ν) * ∑ w, ‖(τ w).1 x‖) ^ N)⁻¹)

theorem tsum_oneMaj (hO : OneVar) (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {m : ℕ} (hm : 0 < m) :
    ∃ K : ℝ≥0, ∀ ν, ∑' x, oneMaj τ m (Module.finrank ℚ E + 1) ν x ≤
      K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * max 0 ν)) := by
  classical
  obtain ⟨K, hK⟩ := hO (mixedEmbedding.mixedSpace E) (mixedEmbedding.integerLattice E) (Module.finrank ℚ E + 1)
    (by rw [mixedEmbedding.finrank]; omega)
  rw [mixedEmbedding.finrank] at hK
  set N := Module.finrank ℚ E + 1
  refine ⟨(m : ℝ≥0) ^ N * K, fun ν => ?_⟩
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let i : {x : E | IsIntegral ℤ ((m : E) * x)} → mixedEmbedding.integerLattice E := fun x =>
    ⟨mixedEmbedding E (m * x.1), ⟨⟨_, x.2⟩, rfl⟩⟩
  have hi : Function.Injective i := fun x y hxy => by
    have := (mixedEmbedding E).injective (congrArg Subtype.val hxy)
    exact Subtype.ext (mul_left_cancel₀ (by exact_mod_cast hm.ne') this)
  have hn : ∀ x : E, ‖mixedEmbedding E x‖ ≤ ∑ w, ‖(τ w).1 x‖ := by
    intro x
    rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
    refine Finset.sup'_le _ _ fun v _ => ?_
    obtain ⟨w, hw⟩ := norm_emb h τ v.embedding
    rw [mixedEmbedding.normAtPlace_apply, ← InfinitePlace.norm_embedding_eq, hw]
    exact Finset.single_le_sum (f := fun w => ‖(τ w).1 x‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  rw [oneMaj, ← tsum_subtype]
  calc _ ≤ ∑' x : {x : E | IsIntegral ℤ ((m : E) * x)}, ((m : ℝ≥0) ^ N : ℝ≥0) *
          ENNReal.ofReal (((1 + Real.exp (-ν) * ‖(i x : mixedEmbedding.mixedSpace E)‖) ^ N)⁻¹) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hS : 0 ≤ ∑ w, ‖(τ w).1 x.1‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
        have h1 : ‖(i x : mixedEmbedding.mixedSpace E)‖ ≤ m * ∑ w, ‖(τ w).1 x.1‖ := by
          refine (hn _).trans (le_of_eq ?_)
          simp [Finset.mul_sum]
        have h2 : 1 + Real.exp (-ν) * ‖(i x : mixedEmbedding.mixedSpace E)‖ ≤
            m * (1 + Real.exp (-ν) * ∑ w, ‖(τ w).1 x.1‖) := by
          have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-ν)).le
          linarith
        have h3 := pow_le_pow_left₀ (by positivity) h2 N
        rw [mul_pow] at h3
        push_cast
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
        exact h3.trans_eq (mul_comm _ _)
    _ ≤ ((m : ℝ≥0) ^ N : ℝ≥0) * (K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * max 0 ν))) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact (ENNReal.tsum_comp_le_tsum_of_injective hi _).trans (hK ν)
    _ = _ := by rw [ENNReal.coe_mul, mul_assoc]

theorem latTor_of : FrameBasis → OneVar → LatTor := by
  intro hB hO F E _ _ _ _ _ σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr'
  classical
  obtain ⟨b, lam, ix, iy, h1, h2, h3, -, hb⟩ := hB F E σ hσ n J hJ fr hfr
  obtain ⟨b', lam', jx, jy, h1', h2', h3', -, hb'⟩ := hB F E σ hσ d J' hJ' fr' hfr'
  set N₀ := Module.finrank ℚ E + 1 with hN₀
  set c := Fintype.card (Fin n × Fin d) with hc
  refine ⟨N₀ * c, fun C hC => ?_⟩
  obtain ⟨m, K, hm, hK, h⟩ := diag_coords τ hfr hfr' hb hb' hC
  obtain ⟨K₁, hK₁⟩ := tsum_oneMaj hO hσ τ hm
  refine ⟨K.toNNReal ^ (N₀ * c) * K₁ ^ c, fun s hs t ht => ?_⟩
  let i : ↥(Set.univ : Set (Matrix (Fin n) (Fin d) E)) → (Fin n × Fin d → E) := fun x p =>
    ((b⁻¹).1 * x.1 * (b'⁻¹).1ᵀ) p.1 p.2
  have hi : Function.Injective i := fun x y hxy => by
    have e : (b⁻¹).1 * x.1 * (b'⁻¹).1ᵀ = (b⁻¹).1 * y.1 * (b'⁻¹).1ᵀ := by
      ext k l
      exact congrFun hxy (k, l)
    have e' : ∀ z : Matrix (Fin n) (Fin d) E, b.1 * ((b⁻¹).1 * z * (b'⁻¹).1ᵀ) * b'.1ᵀ = z := by
      intro z
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
        ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one]
    exact Subtype.ext (by rw [← e' x.1, e, e'])
  let g : (Fin n × Fin d → E) → ℝ≥0∞ := fun ξ => ∏ p, oneMaj τ m N₀ (lam p.1 s + lam' p.2 t) (ξ p)
  calc _ ≤ ∑' x, (K.toNNReal ^ (N₀ * c) : ℝ≥0) * g (i x) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        obtain ⟨ha, hb⟩ := h s t x.1
        unfold maj
        split_ifs with hx
        swap
        · simp
        have hz := sz_nonneg τ (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ)
        set z := sz τ (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ)
        let A : Fin n × Fin d → ℝ := fun p => Real.exp (-(lam p.1 s + lam' p.2 t)) * ∑ w, ‖(τ w).1 (i x p)‖
        have hA0 : ∀ p, 0 ≤ A p := fun p => by positivity
        have hA : ∀ p, 1 + A p ≤ K * (1 + z) := fun p => by
          have : ∑ p, A p ≤ K * z := by
            refine le_trans (le_of_eq ?_) hb
            rw [Fintype.sum_prod_type, Finset.sum_comm (s := (Finset.univ : Finset (InfinitePlace F)))]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_comm (s := (Finset.univ : Finset (InfinitePlace F)))]
            exact Finset.sum_congr rfl fun l _ => Finset.mul_sum _ _ _
          have h4 := Finset.single_le_sum (f := A) (fun p _ => hA0 p) (Finset.mem_univ p)
          linarith
        have hg : g (i x) = ENNReal.ofReal (∏ p, (1 + A p) ^ N₀)⁻¹ := by
          rw [← Finset.prod_inv_distrib, ENNReal.ofReal_prod_of_nonneg fun p _ => by have := hA0 p; positivity]
          exact Finset.prod_congr rfl fun p _ =>
            Set.indicator_of_mem (s := {x | IsIntegral ℤ ((m : E) * x)}) (a := i x p) (ha hx p.1 p.2) _
        have h5 : ∏ p, (1 + A p) ^ N₀ ≤ (K * (1 + z)) ^ (N₀ * c) := by
          rw [pow_mul, hc, ← Finset.card_univ, ← Finset.prod_const]
          exact Finset.prod_le_prod (fun p _ => by have := hA0 p; positivity)
            fun p _ => pow_le_pow_left₀ (by have := hA0 p; positivity) (hA p) _
        have h6 : 0 < ∏ p, (1 + A p) ^ N₀ := Finset.prod_pos fun p _ => by have := hA0 p; positivity
        rw [hg, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        push_cast
        rw [Real.coe_toNNReal _ (by linarith), ← div_eq_mul_inv, le_div_iff₀ h6, inv_mul_le_iff₀ (by positivity),
          ← mul_pow]
        exact h5.trans_eq (by rw [mul_comm K])
    _ ≤ (K.toNNReal ^ (N₀ * c) : ℝ≥0) * ∏ p : Fin n × Fin d, (K₁ * ENNReal.ofReal
          (Real.exp (Module.finrank ℚ E * max 0 (lam p.1 s + lam' p.2 t)))) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        refine (ENNReal.tsum_comp_le_tsum_of_injective hi g).trans ?_
        rw [tsum_fun_prod]
        exact Finset.prod_le_prod' fun p _ => hK₁ _
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hc,
          ← ENNReal.ofReal_prod_of_nonneg fun p _ => (Real.exp_pos _).le, ← Real.exp_sum, ← Finset.mul_sum,
          Fintype.sum_prod_type, sum_pos_lam h1 h2 h3 h1' h2' h3' hs ht]
        push_cast
        rw [mul_assoc]

end PositivityTheory.ThKEst

end
