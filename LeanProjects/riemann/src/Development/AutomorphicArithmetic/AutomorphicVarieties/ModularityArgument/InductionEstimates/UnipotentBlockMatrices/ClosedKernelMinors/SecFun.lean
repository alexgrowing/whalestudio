import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecStr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TensInterp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdMeas
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem locHeight_blk {E : Type} [NormedField E] (a b : GL (Fin 2) E) :
    locHeight (blk a b) ≤ locHeight a * locHeight b := by
  have ha := one_le_locHeight a
  have hb := one_le_locHeight b
  have key : ∀ (A B : Matrix (Fin 2) (Fin 2) E), (∀ i j, ‖A i j‖ ≤ locHeight a) → (∀ i j, ‖B i j‖ ≤ locHeight b) →
      ∀ i j, ‖(Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)) i j‖ ≤ locHeight a * locHeight b := by
    intro A B hA hB i j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j
    · exact (hA i j).trans (le_mul_of_one_le_right (by linarith) hb)
    · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, norm_zero]; positivity
    · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, norm_zero]; positivity
    · exact (hB i j).trans (le_mul_of_one_le_left (by linarith) ha)
  exact locHeight_le (one_le_mul_of_one_le_of_one_le ha hb)
    (key _ _ (norm_apply_le_locHeight a) (norm_apply_le_locHeight b))
    (key _ _ (norm_inv_apply_le_locHeight a) (norm_inv_apply_le_locHeight b))

private theorem map_blk {R S : Type} [CommRing R] [CommRing S] (φ : R → S) (h0 : φ 0 = 0) (a b : GL (Fin 2) R)
    (a' b' : GL (Fin 2) S) (g : GL (Fin (2 + 2)) S) (ha : ∀ i j, a' i j = φ (a i j)) (hb : ∀ i j, b' i j = φ (b i j))
    (hg : ∀ i j, g i j = φ (blk a b i j)) : g = blk a' b' := by
  ext i j
  rw [hg]
  change φ (Matrix.fromBlocks a.val 0 0 b.val (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) =
    Matrix.fromBlocks a'.val 0 0 b'.val (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [h0, ha, hb]

private theorem chain {c M₁ M₂ q x y z u v w : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q) (hz : 0 ≤ z) (hu : 0 ≤ u)
    (h1 : w ≤ c * v * 1) (h2 : v ≤ c * x * u) (h3 : u ≤ c * y * z) (hx : x ≤ |M₁|) (hy : y ≤ 4 * q) (hz' : z ≤ |M₂|) :
    w ≤ c * (c * |M₁| * (c * 4 * |M₂|)) * q := by
  have b3 : u ≤ c * (4 * q) * |M₂| := h3.trans (mul_le_mul (mul_le_mul_of_nonneg_left hy hc) hz' hz (by positivity))
  have b4 : v ≤ c * |M₁| * (c * (4 * q) * |M₂|) :=
    h2.trans (mul_le_mul (mul_le_mul_of_nonneg_left hx hc) b3 hu (by positivity))
  rw [mul_one] at h1
  exact h1.trans ((mul_le_mul_of_nonneg_left b4 hc).trans_eq (by ring))

private theorem height_blk {K : Type} [Field K] [NumberField K] (a b : AdelicGLn.AdelicGL K 2) :
    AutomorphicForm.height (blk a b) ≤ AutomorphicForm.height a * AutomorphicForm.height b := by
  have ei : ∀ w : InfinitePlace K, infAt w (blk a b) = blk (infAt w a) (infAt w b) := fun w =>
    map_blk (fun x : 𝔸[K] => x.1 w) rfl a b (infAt w a) (infAt w b) (infAt w (blk a b)) (infAt_apply w a) (infAt_apply w b)
      (infAt_apply w (blk a b))
  have ef : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), finAt v (blk a b) = blk (finAt v a) (finAt v b) := fun v =>
    map_blk (fun x : 𝔸[K] => x.2 v) rfl a b (finAt v a) (finAt v b) (finAt v (blk a b)) (finAt_apply v a) (finAt_apply v b)
      (finAt_apply v (blk a b))
  generalize blk a b = g at ei ef ⊢
  have h1 : ∏ w : InfinitePlace K, locHeight (infAt w g) ^ w.mult ≤
      (∏ w : InfinitePlace K, locHeight (infAt w a) ^ w.mult) * ∏ w : InfinitePlace K, locHeight (infAt w b) ^ w.mult := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun w _ => (pow_pos (locHeight_pos _) _).le) fun w _ => ?_
    rw [← mul_pow, ei]
    exact pow_le_pow_left₀ (locHeight_pos _).le (locHeight_blk _ _) _
  have fa := finite_mulSupport_locHeight_finAt a
  have fb := finite_mulSupport_locHeight_finAt b
  have h2 := finprod_le_finprod (finite_mulSupport_locHeight_finAt g) (fun v => (locHeight_pos _).le)
    ((fa.union fb).subset (Function.mulSupport_mul _ _)) fun v => by
      rw [ef]; exact locHeight_blk _ _
  rw [finprod_mul_distrib fa fb] at h2
  exact (mul_le_mul h1 h2 (zero_le_one.trans (one_le_finprod_locHeight g))
    (mul_nonneg (zero_le_one.trans (one_le_prod_locHeight a)) (zero_le_one.trans (one_le_prod_locHeight b)))).trans_eq
    (mul_mul_mul_comm _ _ _ _)

private theorem ray_bound (K : Type) [Field K] [NumberField K] (R : ℝ) : ∃ M : ℝ, ∀ t, |t| ≤ R →
    AutomorphicForm.height ((lv (1 : G1 K 2) 1 t : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ≤ |M| := by
  have hlc : Continuous fun t : ℝ => lv (1 : G1 K 2) 1 t :=
    (blkLaws (K := K)).2.2.2.1.comp (f := fun t : ℝ => ((1 : G1 K 2), (1 : G1 K 2), t)) (by fun_prop)
  obtain ⟨M, hM⟩ := exists_height_le_of_isCompact
    ((isCompact_Icc (a := -R) (b := R)).image (continuous_subtype_val.comp hlc))
  exact ⟨M, fun t ht => (hM _ ⟨t, abs_le.1 ht, rfl⟩).trans (le_abs_self _)⟩

private theorem unip_bound (K : Type) [Field K] [NumberField K] : ∃ M : ℝ, ∀ X : UPos (2 + 2) 2 → 𝔸[K],
    ∃ ξ : unipLattice K (2 + 2) 2,
      AutomorphicForm.height ((nn (ξ.1 + X) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ≤ |M| := by
  obtain ⟨D, hD, hsub⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := 2 + 2) (r := 2)
  obtain ⟨M, hM⟩ := exists_height_le_of_isCompact
    (hD.image (continuous_subtype_val.comp (continuous_unipOne (K := K) (n := 2 + 2) 2)))
  refine ⟨M, fun X => ?_⟩
  choose q hq _ using fun p => GroundTheory.Global.existsUnique_sub_mem_fundamentalSet K (X p)
  let ξ : unipLattice K (2 + 2) 2 := ⟨fun p => algebraMap K 𝔸[K] (-q p), fun p => -q p, rfl⟩
  have hξ : ξ.1 + X ∈ D := hsub fun p _ => by
    change algebraMap K 𝔸[K] (-q p) + X p ∈ GroundTheory.Global.fundamentalSet K
    rw [map_neg, neg_add_eq_sub]
    exact hq p
  exact ⟨ξ, (hM _ ⟨_, hξ, rfl⟩).trans (le_abs_self _)⟩

private theorem one_le_qht {K : Type} [Field K] [NumberField K] (m : G1 K 2) : 1 ≤ qht m :=
  le_ciInf fun _ => one_le_height _

private theorem near_qht {K : Type} [Field K] [NumberField K] (m : G1 K 2) : ∃ γ : Gam K 2,
    AutomorphicForm.height (((γ : G1 K 2) * m : G1 K 2) : AdelicGLn.AdelicGL K 2) < 2 * qht m :=
  exists_lt_of_ciInf_lt (show qht m < 2 * qht m by linarith [one_le_qht m])

private theorem height_lv {K : Type} [Field K] [NumberField K] (a b : G1 K 2) :
    AutomorphicForm.height ((lv a b 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ≤
      AutomorphicForm.height (a : AdelicGLn.AdelicGL K 2) * AutomorphicForm.height (b : AdelicGLn.AdelicGL K 2) := by
  have hz : zt K 0 = 1 := by
    rw [zt, ← map_one (centralSection K 2)]
    congr 1
    exact Subtype.ext Real.exp_zero
  rw [blkLaws.1, neg_zero, hz, mul_one, mul_one]
  exact height_blk _ _

private theorem lv_nn {K : Type} [Field K] [NumberField K] (a b m₁ m₂ : G1 K 2) (t : ℝ) (X : UPos (2 + 2) 2 → 𝔸[K])
    (k : G1 K (2 + 2)) : ∃ X', lv a b 0 * (nn X * lv m₁ m₂ t * k) = nn X' * lv (a * m₁) (b * m₂) t * k := by
  obtain ⟨e, he, -⟩ := adMeas a b 0
  refine ⟨e.symm X, ?_⟩
  have h := he (e.symm X)
  rw [ContinuousAddEquiv.apply_symm_apply] at h
  rw [← mul_assoc, ← mul_assoc, ← h, mul_assoc (nn _), blkLaws.2.1, zero_add]

private theorem lv_eq {K : Type} [Field K] [NumberField K] (a b a' b' : G1 K 2) (t : ℝ) (ξ X' : UPos (2 + 2) 2 → 𝔸[K])
    (g k : G1 K (2 + 2)) (h : lv a b 0 * g = nn X' * lv a' b' t * k) :
    nn ξ * lv a b 0 * g = nn (ξ + X') * (lv a' b' 0 * lv 1 1 t) * k := by
  have e1 : lv a' b' 0 * lv 1 1 t = lv a' b' t := by rw [blkLaws.2.1, mul_one, mul_one, zero_add]
  have e2 : nn (ξ + X') = nn ξ * nn X' := unipOne_add 2 ξ X'
  rw [mul_assoc, h, e1, e2]
  simp only [mul_assoc]

private theorem ht_four {K : Type} [Field K] [NumberField K] {n : ℕ} (x y z k : G1 K n) (hk : k ∈ KG K n) {M₁ M₂ q : ℝ}
    (hq : 0 ≤ q) (hx : AutomorphicForm.height (x : AdelicGLn.AdelicGL K n) ≤ |M₁|)
    (hy : AutomorphicForm.height (y : AdelicGLn.AdelicGL K n) ≤ 4 * q)
    (hz : AutomorphicForm.height (z : AdelicGLn.AdelicGL K n) ≤ |M₂|) :
    AutomorphicForm.height ((x * (y * z) * k : G1 K n) : AdelicGLn.AdelicGL K n) ≤
      heightConst K n * (heightConst K n * |M₁| * (heightConst K n * 4 * |M₂|)) * q := by
  have h := height_mul_le ((x : AdelicGLn.AdelicGL K n) * ((y : AdelicGLn.AdelicGL K n) * (z : AdelicGLn.AdelicGL K n))) (k : AdelicGLn.AdelicGL K n)
  rw [height_eq_one_of_mem_maxCompact (k := (k : AdelicGLn.AdelicGL K n)) hk] at h
  exact chain (zero_le_one.trans one_le_heightConst) hq (height_pos _).le (height_pos _).le h (height_mul_le _ _)
    (height_mul_le _ _) hx hy hz

private theorem ht_bound {K : Type} [Field K] [NumberField K] (R : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ (X : UPos (2 + 2) 2 → 𝔸[K]) (m₁ m₂ : G1 K 2) (t : ℝ), ∀ k ∈ KG K (2 + 2), |t| ≤ R → ∃ γ ∈ PK K,
      AutomorphicForm.height ((γ * (nn X * lv m₁ m₂ t * k) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ≤
        M * (qht m₁ * qht m₂) := by
  obtain ⟨M₁, hM₁⟩ := unip_bound K
  obtain ⟨M₂, hM₂⟩ := ray_bound K R
  have hc : 0 ≤ heightConst K (2 + 2) := zero_le_one.trans one_le_heightConst
  refine ⟨heightConst K (2 + 2) * (heightConst K (2 + 2) * |M₁| * (heightConst K (2 + 2) * 4 * |M₂|)),
    mul_nonneg hc (mul_nonneg (mul_nonneg hc (abs_nonneg _)) (mul_nonneg (mul_nonneg hc zero_le_four) (abs_nonneg _))),
    fun X m₁ m₂ t k hk ht => ?_⟩
  have h1 := zero_le_one.trans (one_le_qht m₁)
  have h2 := zero_le_one.trans (one_le_qht m₂)
  obtain ⟨γ₁, hγ₁⟩ := near_qht m₁
  obtain ⟨γ₂, hγ₂⟩ := near_qht m₂
  obtain ⟨X', hX'⟩ := lv_nn (γ₁ : G1 K 2) γ₂ m₁ m₂ t X k
  obtain ⟨ξ, b1⟩ := hM₁ X'
  refine ⟨nn ξ.1 * lv (γ₁ : G1 K 2) γ₂ 0, (pkLaws.2.1 _).2 ⟨ξ, γ₁, γ₂, rfl⟩, ?_⟩
  have b0 : AutomorphicForm.height ((lv ((γ₁ : G1 K 2) * m₁) ((γ₂ : G1 K 2) * m₂) 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ≤
      4 * (qht m₁ * qht m₂) :=
    ((height_lv ((γ₁ : G1 K 2) * m₁) ((γ₂ : G1 K 2) * m₂)).trans
      (mul_le_mul hγ₁.le hγ₂.le (height_pos _).le (mul_nonneg zero_le_two h1))).trans_eq (by ring)
  have e := lv_eq (γ₁ : G1 K 2) γ₂ ((γ₁ : G1 K 2) * m₁) ((γ₂ : G1 K 2) * m₂) t ξ.1 X' (nn X * lv m₁ m₂ t * k) k hX'
  rw [e]
  exact ht_four (nn (ξ.1 + X')) (lv ((γ₁ : G1 K 2) * m₁) ((γ₂ : G1 K 2) * m₂) 0) (lv 1 1 t) k hk (mul_nonneg h1 h2) b1 b0 (hM₂ t ht)

private theorem cusp_sum {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)} {τ : Submodule ℂ (L2 μ₂)} {a b : ℕ}
    (φ : Fin a → G1 K 2 → ℂ) (hφ : ∀ i, Rd τ (φ i)) (c : Fin b → Fin a → ℂ) (m : G1 K 2) :
    ∫ Y in unipFundamentalDomain K 2 1, ∑ j, ∑ i, c j i * φ i (unipOne K 2 1 Y * m) ∂unipMeasure K 2 1 = 0 := by
  obtain ⟨D, hD, hsub⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := 2) (r := 1)
  have hi : ∀ j i, Integrable (fun Y => c j i * φ i (unipOne K 2 1 Y * m))
      ((unipMeasure K 2 1).restrict (unipFundamentalDomain K 2 1)) := fun j i =>
    ((continuous_const.mul ((hφ i).cont.comp ((continuous_unipOne 1).mul continuous_const))).continuousOn.integrableOn_compact
      hD).mono_set hsub
  rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun i _ => hi j i]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_finset_sum _ fun i _ => hi j i]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul, (hφ i).cusp, mul_zero]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.secFun :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2)), CuspIrr μ₂ τ₁ → CuspIrr μ₂ τ₂ → ∀ f : G1 K (2 + 2) → ℂ, IsSec τ₁ τ₂ f → D.Fix f → SFun f := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ D h₁ h₂ f hf hD
  obtain ⟨hc, ⟨B, hB⟩, hu, hr, hs⟩ := (secCrit μ₂ τ₁ τ₂ D h₁ h₂ f hD).1 hf
  obtain ⟨E₁, E₂, i₁, i₂, r₁, r₂, hE⟩ := secStr μ₂ τ₁ τ₂ D h₁ h₂
  obtain ⟨a, b, φ, ψ, x, y, s, s', hφ, hψ, hT⟩ := tens E₁ E₂
  let c : G1 K (2 + 2) → Fin a → Fin b → ℂ := fun k i j => ∑ p, ∑ q, s i p * s' j q * f (lv (x i p) (y j q) 0 * k)
  have hcb : ∀ k i j, ‖c k i j‖ ≤ ∑ p, ∑ q, ‖s i p * s' j q‖ * B := fun k i j =>
    norm_sum_le_of_le _ fun p _ => norm_sum_le_of_le _ fun q _ => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  have rep : ∀ X m₁ m₂ t, ∀ k ∈ KG K (2 + 2), f (nn X * lv m₁ m₂ t * k) = ∑ i, ∑ j, c k i j * φ i m₁ * ψ j m₂ := by
    intro X m₁ m₂ t k hk
    have e : lv m₁ m₂ t = lv 1 1 t * lv m₁ m₂ 0 := by rw [blkLaws.2.1, one_mul, one_mul, add_zero]
    rw [mul_assoc, hu, e, mul_assoc, hr]
    exact hT (fun u v => f (lv u v 0 * k)) (hE f hc hD hs k hk).1 (hE f hc hD hs k hk).2 m₁ m₂
  have rep' : ∀ u v X m₁ m₂ t, ∀ k ∈ KG K (2 + 2), f (lv u v 0 * (nn X * lv m₁ m₂ t * k)) =
      ∑ i, ∑ j, c k i j * φ i (u * m₁) * ψ j (v * m₂) := by
    intro u v X m₁ m₂ t k hk
    obtain ⟨X', hX'⟩ := lv_nn u v m₁ m₂ t X k
    rw [hX', rep _ _ _ _ k hk]
  refine ⟨⟨hc, ⟨B, hB⟩, hu, fun γ hγ g => ?_, fun g => ?_, fun g => ?_⟩, hr, fun N R => ?_⟩
  · obtain ⟨ξ, γ₁, γ₂, rfl⟩ := (pkLaws.2.1 γ).1 hγ
    obtain ⟨X, m₁, m₂, t, k, hk, rfl⟩ := iwa g
    rw [mul_assoc, hu, rep' _ _ _ _ _ _ k hk, rep _ _ _ _ k hk]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [(r₁ _ (hφ i)).rat _ γ₁.2, (r₂ _ (hψ j)).rat _ γ₂.2]
  · obtain ⟨X, m₁, m₂, t, k, hk, rfl⟩ := iwa g
    rw [← cusp_sum φ (fun i => r₁ _ (hφ i)) (fun j i => c k i j * ψ j (1 * m₂)) m₁]
    congr 1
    funext Y
    rw [rep' _ _ _ _ _ _ k hk, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · obtain ⟨X, m₁, m₂, t, k, hk, rfl⟩ := iwa g
    rw [← cusp_sum ψ (fun i => r₂ _ (hψ i)) (fun i j => c k i j * φ i (1 * m₁)) m₂]
    congr 1
    funext Y
    rw [rep' _ _ _ _ _ _ k hk]
  · obtain ⟨M, hM0, hM⟩ := ht_bound (K := K) R
    choose C₁ hC₁ using fun i => (r₁ _ (hφ i)).decay N
    choose C₂ hC₂ using fun j => (r₂ _ (hψ j)).decay N
    refine ⟨∑ i, ∑ j, M ^ N * ((∑ p, ∑ q, ‖s i p * s' j q‖ * B) * (C₁ i * C₂ j)), fun g hg => ?_⟩
    obtain ⟨X, m₁, m₂, t, k, hk, rfl⟩ := iwa g
    rw [hpSpec.1, (hpSpec.2.1 k hk).1, add_zero] at hg
    obtain ⟨γ, hγ, hle⟩ := hM X m₁ m₂ t k hk hg
    refine ⟨γ, hγ, ?_⟩
    have h1 := zero_le_one.trans (one_le_qht m₁)
    have h2 := zero_le_one.trans (one_le_qht m₂)
    refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le hle N) (norm_nonneg _)).trans ?_
    rw [rep _ _ _ _ k hk]
    refine (mul_le_mul_of_nonneg_right (norm_sum_le_of_le _ fun i _ => norm_sum_le _ _) (pow_nonneg (mul_nonneg hM0 (mul_nonneg h1 h2)) N)).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have e : ‖c k i j * φ i m₁ * ψ j m₂‖ * (M * (qht m₁ * qht m₂)) ^ N =
        M ^ N * (‖c k i j‖ * ((‖φ i m₁‖ * qht m₁ ^ N) * (‖ψ j m₂‖ * qht m₂ ^ N))) := by
      rw [norm_mul, norm_mul, mul_pow, mul_pow]; ring
    rw [e]
    have p1 : 0 ≤ ‖φ i m₁‖ * qht m₁ ^ N := mul_nonneg (norm_nonneg _) (pow_nonneg h1 N)
    have p2 : 0 ≤ ‖ψ j m₂‖ * qht m₂ ^ N := mul_nonneg (norm_nonneg _) (pow_nonneg h2 N)
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hcb k i j) (mul_le_mul (hC₁ i m₁) (hC₂ j m₂) p2 (p1.trans (hC₁ i m₁)))
      (mul_nonneg p1 p2) ((norm_nonneg _).trans (hcb k i j))) (pow_nonneg hM0 N)
