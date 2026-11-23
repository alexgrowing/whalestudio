import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelConj
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private theorem entry_le {E : Type*} [NormedField E] {n : ℕ} (b m b' : GL (Fin n) E)
    (d : Fin n → Eˣ) (ρ : Fin n → ℝ) (hd : ∀ i, ‖((d i : Eˣ) : E)‖ = ρ i) (hρ : ∀ i, 0 < ρ i)
    (hb : ∀ p q : Fin n, q < p → (b : Matrix (Fin n) (Fin n) E) p q = 0)
    (hb' : ∀ p q : Fin n, q < p → (b' : Matrix (Fin n) (Fin n) E) p q = 0)
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) (hr : ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → ρ j / ρ i ≤ ε)
    (i j : Fin n) (hi : (i : ℕ) < r) (hj : r ≤ (j : ℕ)) :
    ‖((b * diagUnits n d * m * (diagUnits n d)⁻¹ * b' : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E) j i‖ ≤
      (n : ℝ) ^ 2 * ε * (AutomorphicForm.locHeight b * AutomorphicForm.locHeight m *
        AutomorphicForm.locHeight b') := by
  have hinv : (((diagUnits n d)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      Matrix.diagonal fun i => (((d i)⁻¹ : Eˣ) : E) := by
    rw [← map_inv, coe_diagUnits]; rfl
  have e : ((b * diagUnits n d * m * (diagUnits n d)⁻¹ * b' : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E) j i =
      ∑ q, ∑ p, (b : Matrix (Fin n) (Fin n) E) j p * ((d p : Eˣ) : E) *
        (m : Matrix (Fin n) (Fin n) E) p q * (((d q)⁻¹ : Eˣ) : E) *
        (b' : Matrix (Fin n) (Fin n) E) q i := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, hinv, coe_diagUnits,
      Matrix.mul_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by rw [Matrix.mul_diagonal]
  have hL : 0 ≤ AutomorphicForm.locHeight b * AutomorphicForm.locHeight m *
      AutomorphicForm.locHeight b' := by
    have h1 := AutomorphicForm.locHeight_pos b
    have h2 := AutomorphicForm.locHeight_pos m
    have h3 := AutomorphicForm.locHeight_pos b'
    positivity
  have term : ∀ p q : Fin n, ‖(b : Matrix (Fin n) (Fin n) E) j p * ((d p : Eˣ) : E) *
        (m : Matrix (Fin n) (Fin n) E) p q * (((d q)⁻¹ : Eˣ) : E) *
        (b' : Matrix (Fin n) (Fin n) E) q i‖ ≤
      ε * (AutomorphicForm.locHeight b * AutomorphicForm.locHeight m *
        AutomorphicForm.locHeight b') := by
    intro p q
    by_cases h1 : p < j
    · rw [hb j p h1]; simpa using mul_nonneg hε.le hL
    by_cases h2 : i < q
    · rw [hb' q i h2]; simpa using mul_nonneg hε.le hL
    have hp : r ≤ (p : ℕ) := hj.trans (Fin.not_lt.1 h1)
    have hq : (q : ℕ) < r := lt_of_le_of_lt (Fin.not_lt.1 h2) hi
    have hratio := hr q p hq hp
    have hq0 := hρ q
    have e2 : ‖(b : Matrix (Fin n) (Fin n) E) j p * ((d p : Eˣ) : E) *
        (m : Matrix (Fin n) (Fin n) E) p q * (((d q)⁻¹ : Eˣ) : E) *
        (b' : Matrix (Fin n) (Fin n) E) q i‖ =
        ρ p / ρ q * (‖(b : Matrix (Fin n) (Fin n) E) j p‖ * ‖(m : Matrix (Fin n) (Fin n) E) p q‖ *
          ‖(b' : Matrix (Fin n) (Fin n) E) q i‖) := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hd, hd]
      field_simp
    rw [e2]
    refine mul_le_mul hratio ?_ (by positivity) hε.le
    exact mul_le_mul (mul_le_mul (AutomorphicForm.norm_apply_le_locHeight b j p)
      (AutomorphicForm.norm_apply_le_locHeight m p q) (norm_nonneg _)
      (AutomorphicForm.locHeight_pos b).le) (AutomorphicForm.norm_apply_le_locHeight b' q i)
      (norm_nonneg _) (mul_nonneg (AutomorphicForm.locHeight_pos b).le
        (AutomorphicForm.locHeight_pos m).le)
  rw [e]
  calc _ ≤ ∑ _q : Fin n, ∑ _p : Fin n, ε * (AutomorphicForm.locHeight b *
        AutomorphicForm.locHeight m * AutomorphicForm.locHeight b') :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => term p q))
    _ = _ := by simp; ring

theorem UpperTheory.one_le_entry_bound_of_borel_diagonal_decomp :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (δ : GL (Fin n) K) (b b' m : AdelicGLn.AdelicGL K n),
          b ∈ (adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) → b' ∈ (adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) →
          ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i) (r : ℕ) (ε : ℝ), 0 < ε →
          (∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → ρ j / ρ i ≤ ε) →
          AdelicGLn.diagonal K n δ = b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * m *
            (diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)))⁻¹ * b' →
          ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → (δ : Matrix (Fin n) (Fin n) K) j i ≠ 0 →
          1 ≤ ((n : ℝ) ^ 2 * ε) ^ Module.finrank ℚ K * (AutomorphicForm.heightConst K n *
            (AutomorphicForm.height b * AutomorphicForm.height m * AutomorphicForm.height b')) ^ 2 := by
  intro K _ _ n δ b b' m hb hb' ρ hρ r ε hε hr hδ i j hi hj hc
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      finAt v (diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i))) = 1 := by
    intro v
    refine Units.ext (Matrix.ext fun p q => ?_)
    rw [finAt_apply, coe_diagUnits, Matrix.diagonal_apply, Units.val_one, Matrix.one_apply]
    split_ifs with h
    · subst h
      exact posIdele_finite (K := K) (ρ p) (hρ p) v
    · rfl
  have hv : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖(((δ : Matrix (Fin n) (Fin n) K) j i : K) : v.adicCompletion K)‖ ≤
        AutomorphicForm.locHeight (finAt v (b * m * b')) := by
    intro v
    have h1 : finAt v (AdelicGLn.diagonal K n δ) = finAt v (b * m * b') := by
      rw [hδ]
      simp only [finAt_mul, finAt_inv, hfin, mul_one, inv_one]
    have h2 := AutomorphicForm.norm_apply_le_locHeight (finAt v (b * m * b')) j i
    rw [← h1, finAt_apply, AdelicGLn.diagonal_apply] at h2
    rw [h1] at h2
    exact h2
  have hw : ∀ w : InfinitePlace K,
      ‖(((δ : Matrix (Fin n) (Fin n) K) j i : K) : w.Completion)‖ ≤
        (n : ℝ) ^ 2 * ε * (AutomorphicForm.locHeight (infAt w b) *
          AutomorphicForm.locHeight (infAt w m) * AutomorphicForm.locHeight (infAt w b')) := by
    intro w
    have h1 : infAt w (AdelicGLn.diagonal K n δ) =
        infAt w b * diagUnits n (fun i => posRealToUnits w ⟨ρ i ^ w.mult, pow_pos (hρ i) _⟩) *
          infAt w m * (diagUnits n (fun i => posRealToUnits w ⟨ρ i ^ w.mult, pow_pos (hρ i) _⟩))⁻¹ *
          infAt w b' := by
      rw [hδ]
      simp only [infAt_mul, infAt_inv, infAt_diagUnits_posIdele]
    have h2 := entry_le (infAt w b) (infAt w m) (infAt w b')
      (fun i => posRealToUnits w ⟨ρ i ^ w.mult, pow_pos (hρ i) _⟩) ρ
      (fun i => norm_posRealToUnits w (hρ i)) hρ
      (fun p q h => by rw [infAt_apply, mem_adelicBorel.1 hb h]; rfl)
      (fun p q h => by rw [infAt_apply, mem_adelicBorel.1 hb' h]; rfl)
      r ε hε hr i j hi hj
    rw [← h1, infAt_apply, AdelicGLn.diagonal_apply] at h2
    exact h2
  have hN : 0 ≤ (n : ℝ) ^ 2 * ε := by positivity
  have pb := AutomorphicForm.height_pos b
  have pm := AutomorphicForm.height_pos m
  have pb' := AutomorphicForm.height_pos b'
  have hC := AutomorphicForm.one_le_heightConst (K := K) (n := n)
  have inf_le : ∀ g : AdelicGLn.AdelicGL K n,
      ∏ w : InfinitePlace K, AutomorphicForm.locHeight (infAt w g) ^ w.mult ≤
        AutomorphicForm.height g := fun g =>
    le_mul_of_one_le_right (zero_le_one.trans (AutomorphicForm.one_le_prod_locHeight g))
      (AutomorphicForm.one_le_finprod_locHeight g)
  have hI : ∏ w : InfinitePlace K, ‖(((δ : Matrix (Fin n) (Fin n) K) j i : K) : w.Completion)‖ ^ w.mult ≤
      ((n : ℝ) ^ 2 * ε) ^ Module.finrank ℚ K *
        (AutomorphicForm.height b * AutomorphicForm.height m * AutomorphicForm.height b') := by
    calc _ ≤ ∏ w : InfinitePlace K, ((n : ℝ) ^ 2 * ε * (AutomorphicForm.locHeight (infAt w b) *
          AutomorphicForm.locHeight (infAt w m) * AutomorphicForm.locHeight (infAt w b'))) ^ w.mult :=
          Finset.prod_le_prod (fun _ _ => pow_nonneg (norm_nonneg _) _)
            fun w _ => pow_le_pow_left₀ (norm_nonneg _) (hw w) _
      _ = ((n : ℝ) ^ 2 * ε) ^ Module.finrank ℚ K *
          ((∏ w : InfinitePlace K, AutomorphicForm.locHeight (infAt w b) ^ w.mult) *
           (∏ w : InfinitePlace K, AutomorphicForm.locHeight (infAt w m) ^ w.mult) *
           (∏ w : InfinitePlace K, AutomorphicForm.locHeight (infAt w b') ^ w.mult)) := by
          rw [← InfinitePlace.sum_mult_eq (K := K), ← Finset.prod_pow_eq_pow_sum]
          simp only [mul_pow, Finset.prod_mul_distrib]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hN _)
          have q1 := zero_le_one.trans (AutomorphicForm.one_le_prod_locHeight b)
          have q2 := zero_le_one.trans (AutomorphicForm.one_le_prod_locHeight m)
          have q3 := zero_le_one.trans (AutomorphicForm.one_le_prod_locHeight b')
          exact mul_le_mul (mul_le_mul (inf_le b) (inf_le m) q2 pb.le) (inf_le b') q3 (by positivity)
  have hF : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(((δ : Matrix (Fin n) (Fin n) K) j i : K) : v.adicCompletion K)‖ ≤
      AutomorphicForm.heightConst K n ^ 2 *
        (AutomorphicForm.height b * AutomorphicForm.height m * AutomorphicForm.height b') := by
    calc _ ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.locHeight (finAt v (b * m * b')) :=
          finprod_le_finprod (Filter.eventually_cofinite.1 (eventually_norm_eq_one hc))
            (fun _ => norm_nonneg _) (AutomorphicForm.finite_mulSupport_locHeight_finAt _) hv
      _ ≤ AutomorphicForm.height (b * m * b') :=
          le_mul_of_one_le_left (zero_le_one.trans (AutomorphicForm.one_le_finprod_locHeight _))
            (AutomorphicForm.one_le_prod_locHeight _)
      _ ≤ AutomorphicForm.heightConst K n * AutomorphicForm.height (b * m) * AutomorphicForm.height b' :=
          AutomorphicForm.height_mul_le _ _
      _ ≤ AutomorphicForm.heightConst K n * (AutomorphicForm.heightConst K n *
            AutomorphicForm.height b * AutomorphicForm.height m) * AutomorphicForm.height b' := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (AutomorphicForm.height_mul_le _ _) (zero_le_one.trans hC)) pb'.le
      _ = _ := by ring
  have hC0 : 0 < AutomorphicForm.heightConst K n := zero_lt_one.trans_le hC
  calc (1 : ℝ) = _ := (prod_norm_mul_finprod_norm hc).symm
    _ ≤ (((n : ℝ) ^ 2 * ε) ^ Module.finrank ℚ K *
          (AutomorphicForm.height b * AutomorphicForm.height m * AutomorphicForm.height b')) *
        (AutomorphicForm.heightConst K n ^ 2 *
          (AutomorphicForm.height b * AutomorphicForm.height m * AutomorphicForm.height b')) :=
        mul_le_mul hI hF (finprod_nonneg fun _ => norm_nonneg _) (by positivity)
    _ = _ := by ring
