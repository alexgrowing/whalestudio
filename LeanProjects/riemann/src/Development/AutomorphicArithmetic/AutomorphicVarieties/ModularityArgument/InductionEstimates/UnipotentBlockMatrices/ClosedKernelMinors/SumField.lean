import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem tsum_fin {α : Type} (f : α → ℝ≥0∞) (k : ℕ) :
    ∑' x : Fin k → α, ∏ i, f (x i) = (∑' a, f a) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← (Fin.consEquiv fun _ : Fin (k + 1) => α).tsum_eq, ENNReal.tsum_prod', pow_succ', ← ih,
      ← ENNReal.tsum_mul_right]
    refine tsum_congr fun a => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun x => ?_
    simp [Fin.prod_univ_succ, Fin.consEquiv]

private theorem tsum_pi {α ι : Type} [Fintype ι] (f : α → ℝ≥0∞) :
    ∑' x : ι → α, ∏ i, f (x i) = (∑' a, f a) ^ Fintype.card ι := by
  rw [← tsum_fin, ← (Equiv.arrowCongr (Fintype.equivFin ι) (Equiv.refl α)).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [← (Fintype.equivFin ι).prod_comp]
  simp

private theorem step {α β ι : Type} [Fintype ι] (e : β → ι → α) (he : Function.Injective e) (f : α → ℝ)
    (hf : ∀ a, 0 < f a) (hs : ∑' a, ENNReal.ofReal (f a)⁻¹ ≠ ⊤) (H : β → ℝ) (hH : ∀ b, 0 < H b) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ b i, f (e b i) ≤ C * H b) : ∑' b, ENNReal.ofReal (H b ^ Fintype.card ι)⁻¹ ≠ ⊤ := by
  have h1 : ∀ b, ENNReal.ofReal (H b ^ Fintype.card ι)⁻¹ ≤
      ENNReal.ofReal (C ^ Fintype.card ι) * ∏ i, ENNReal.ofReal (f (e b i))⁻¹ := by
    intro b
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => (inv_pos.2 (hf _)).le, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← inv_pow, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun _ _ => (inv_pos.2 (hH b)).le) fun i _ => ?_
    rw [← div_eq_mul_inv, le_div_iff₀ (hf _), inv_mul_le_iff₀ (hH b), mul_comm]
    exact h b i
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum h1)
  rw [ENNReal.tsum_mul_left]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top ?_
    (ENNReal.tsum_comp_le_tsum_of_injective he fun x : ι → α => ∏ i, ENNReal.ofReal (f (x i))⁻¹))
  rw [tsum_pi fun a => ENNReal.ofReal (f a)⁻¹]
  exact ENNReal.pow_ne_top hs

private theorem sum_int : ∑' a : ℤ, ENNReal.ofReal (max 1 ((a : ℝ) ^ 2))⁻¹ ≠ ⊤ := by
  refine Summable.tsum_ofReal_ne_top ?_
  have h : Summable fun a : ℤ => 1 / (a : ℝ) ^ 2 := Real.summable_one_div_int_pow.2 one_lt_two
  refine h.congr_cofinite ?_
  refine (Set.finite_singleton (0 : ℤ)).subset fun a ha => ?_
  by_contra h0
  refine ha ?_
  have h1 : (1 : ℤ) ≤ a ^ 2 := (one_le_sq_iff_one_le_abs a).2 (Int.one_le_abs h0)
  have h2 : (1 : ℝ) ≤ (a : ℝ) ^ 2 := by exact_mod_cast h1
  show 1 / (a : ℝ) ^ 2 = (max 1 ((a : ℝ) ^ 2))⁻¹
  rw [max_eq_right h2, one_div]

private theorem inf_le {K : Type} [Field K] [NumberField K] (x : K) (w : InfinitePlace K) :
    w x ≤ Height.mulHeight₁ x := by
  classical
  rw [mulHeight₁_eq]
  have h1 : (1 : ℝ) ≤ ∏ᶠ v : FinitePlace K, max (v x) 1 :=
    finprod_induction (fun x : ℝ => 1 ≤ x) le_rfl (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy)
      fun _ => le_max_right _ _
  have h2 : max (w x) 1 ^ w.mult ≤ ∏ v : InfinitePlace K, max (v x) 1 ^ v.mult := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
    exact le_mul_of_one_le_right (by positivity) (Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
      (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl fun _ _ => one_le_pow₀ (le_max_right _ _))
  have h3 : w x ≤ max (w x) 1 ^ w.mult :=
    (le_max_left _ _).trans (le_self_pow₀ (le_max_right _ _) w.mult_ne_zero)
  exact (h3.trans h2).trans (le_mul_of_one_le_right ((apply_nonneg w x).trans (h3.trans h2)) h1)

private theorem sum_field (K : Type) [Field K] [NumberField K] :
    ∃ M : ℕ, ∑' x : K, ENNReal.ofReal (Height.mulHeight₁ x ^ M)⁻¹ ≠ ⊤ := by
  obtain ⟨C, hC, hr⟩ := exists_abs_repr_le K
  choose m hm0 hm hi using fun x : K => exists_nat_le_mulHeight₁ x
  let z : K → 𝓞 K := fun x => ⟨m x * x, hi x⟩
  let e : K → Option (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) → ℤ := fun x o =>
    o.elim (m x) fun i => (RingOfIntegers.basis K).repr (z x) i
  have he : Function.Injective e := by
    intro x y h
    have h1 : m x = m y := Int.natCast_inj.1 (congrFun h none)
    have h2 : z x = z y := (RingOfIntegers.basis K).repr.injective (Finsupp.ext fun i => congrFun h (some i))
    have h3 : (m x : K) * x = m y * y := congrArg Subtype.val h2
    rw [h1] at h3
    exact mul_left_cancel₀ (Nat.cast_ne_zero.2 (hm0 y)) h3
  have := step e he (fun a => max 1 ((a : ℝ) ^ 2)) (fun _ => lt_max_of_lt_left one_pos) sum_int
    (fun x => Height.mulHeight₁ x ^ 4) (fun x => pow_pos (Height.mulHeight₁_pos x) 4)
    (C := (max 1 C) ^ 2) (by positivity) ?_
  · exact ⟨_, by simpa only [← pow_mul] using this⟩
  intro x o
  have hH := Height.one_le_mulHeight₁ x
  have hC1 : 1 ≤ max 1 C := le_max_left _ _
  have hb : |(e x o : ℝ)| ≤ max 1 C * Height.mulHeight₁ x ^ 2 := by
    cases o with
    | none =>
      change |((m x : ℤ) : ℝ)| ≤ _
      rw [Int.cast_natCast, Nat.abs_cast]
      exact ((hm x).trans (le_self_pow₀ hH two_ne_zero)).trans (le_mul_of_one_le_left (by positivity) hC1)
    | some i =>
      refine (hr (z x) i).trans ((mul_le_mul_of_nonneg_left ?_ hC).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
      rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
      refine Finset.sup'_le _ _ fun w _ => ?_
      rw [mixedEmbedding.normAtPlace_apply]
      change w ((m x : K) * x) ≤ _
      rw [map_mul, InfinitePlace.map_natCast, sq]
      exact mul_le_mul (hm x) (inf_le x w) (apply_nonneg _ _) (by positivity)
  refine max_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1) (one_le_pow₀ hH)) ?_
  calc _ = |(e x o : ℝ)| ^ 2 := (sq_abs _).symm
    _ ≤ (max 1 C * Height.mulHeight₁ x ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = _ := by ring

private theorem entry_le {K : Type} [Field K] [NumberField K] {n : ℕ} (γ : GL (Fin n) K) (i j : Fin n) :
    Height.mulHeight₁ (γ.val i j) ≤ AutomorphicForm.height (AdelicGLn.diagonal K n γ) := by
  rw [mulHeight₁_eq, AutomorphicForm.height, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
  have hf : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      max (FinitePlace.equivHeightOneSpectrum.symm v (γ.val i j)) 1 ≤ locHeight (finAt v (AdelicGLn.diagonal K n γ)) :=
    fun v => max_le (norm_apply_le_locHeight (finAt v (AdelicGLn.diagonal K n γ)) i j) (one_le_locHeight _)
  refine mul_le_mul ?_ ?_ (finprod_nonneg fun _ => le_max_of_le_right zero_le_one)
    (zero_le_one.trans (one_le_prod_locHeight _))
  · refine Finset.prod_le_prod (fun _ _ => by positivity) fun w _ => ?_
    refine pow_le_pow_left₀ (by positivity) (max_le ?_ (one_le_locHeight _)) _
    refine le_trans (le_of_eq ?_) (norm_apply_le_locHeight (infAt w (AdelicGLn.diagonal K n γ)) i j)
    exact (InfinitePlace.Completion.norm_coe w _).symm
  · refine finprod_le_finprod ((finite_mulSupport_locHeight_finAt (AdelicGLn.diagonal K n γ)).subset fun v hv h1 => hv ?_)
      (fun _ => le_max_of_le_right zero_le_one) (finite_mulSupport_locHeight_finAt _) hf
    exact le_antisymm ((hf v).trans_eq h1) (le_max_right _ _)

private theorem sum_gam (K : Type) [Field K] [NumberField K] (n : ℕ) : ∃ M : ℕ,
    ∑' γ : Gam K n, ENNReal.ofReal (AutomorphicForm.height ((γ : G1 K n) : AdelicGLn.AdelicGL K n) ^ M)⁻¹ ≠ ⊤ := by
  obtain ⟨M, hM⟩ := sum_field K
  have hγ : ∀ γ : Gam K n, ∃ δ : GL (Fin n) K, AdelicGLn.diagonal K n δ = ((γ : G1 K n) : AdelicGLn.AdelicGL K n) :=
    fun γ => γ.2
  choose δ hδ using hγ
  have := step (fun (γ : Gam K n) (p : Fin n × Fin n) => (δ γ).val p.1 p.2) ?_ (fun x => Height.mulHeight₁ x ^ M)
    (fun x => pow_pos (Height.mulHeight₁_pos x) M) hM
    (fun γ => AutomorphicForm.height ((γ : G1 K n) : AdelicGLn.AdelicGL K n) ^ M) (fun γ => pow_pos (height_pos _) M)
    zero_le_one ?_
  · exact ⟨_, by simpa only [← pow_mul] using this⟩
  · intro γ γ' h
    have : δ γ = δ γ' := Units.ext (Matrix.ext fun i j => congrFun h (i, j))
    exact Subtype.ext (Subtype.ext (by rw [← hδ, ← hδ, this]))
  · intro γ p
    rw [one_mul, ← hδ]
    exact pow_le_pow_left₀ (Height.mulHeight₁_pos _).le (entry_le _ _ _) M

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.sumHt :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ), ∃ (N : ℕ) (C : ℝ≥0∞), C ≠ ⊤ ∧ ∀ g : G1 K n,
      ∑' γ : Gam K n, ENNReal.ofReal ((AutomorphicForm.height (((γ : G1 K n) * g : G1 K n) : AdelicGLn.AdelicGL K n) ^ N)⁻¹) ≤ C := by
  intro K _ _ n
  obtain ⟨M, hM⟩ := sum_gam K n
  have hc : 0 < heightConst K n := one_pos.trans_le one_le_heightConst
  refine ⟨2 * M, _, ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := (heightConst K n * 2) ^ M)) hM, fun g => ?_⟩
  set F : Gam K n → ℝ := fun γ => AutomorphicForm.height (((γ : G1 K n) * g : G1 K n) : AdelicGLn.AdelicGL K n) with hF
  have hF1 : ∀ γ, 1 ≤ F γ := fun γ => one_le_height _
  have hb : BddBelow (Set.range F) := ⟨1, Set.forall_mem_range.2 hF1⟩
  have hi : 1 ≤ ⨅ γ, F γ := le_ciInf hF1
  obtain ⟨γ₀, h₀⟩ := exists_lt_of_ciInf_lt (f := F) (a := 2 * ⨅ γ, F γ) (by linarith)
  rw [← (Equiv.mulRight γ₀⁻¹).tsum_eq fun γ : Gam K n =>
    ENNReal.ofReal (AutomorphicForm.height ((γ : G1 K n) : AdelicGLn.AdelicGL K n) ^ M)⁻¹, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun γ => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  change (F γ ^ (2 * M))⁻¹ ≤ _
  have hp : 0 < F γ := one_pos.trans_le (hF1 γ)
  rw [pow_mul, ← inv_pow _ M, ← inv_pow _ M, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ M
  rw [← div_eq_mul_inv, le_div_iff₀ (height_pos _), inv_mul_le_iff₀ (by positivity)]
  have e : (((Equiv.mulRight γ₀⁻¹ γ : Gam K n) : G1 K n) : AdelicGLn.AdelicGL K n) =
      (((γ : G1 K n) * g : G1 K n) : AdelicGLn.AdelicGL K n) *
        ((((γ₀ : G1 K n) * g : G1 K n) : AdelicGLn.AdelicGL K n))⁻¹ := by
    simp [mul_assoc]
  rw [e]
  refine (height_mul_le _ _).trans ?_
  rw [height_inv]
  have h2 : F γ₀ ≤ 2 * F γ := h₀.le.trans (by linarith [ciInf_le hb γ])
  calc heightConst K n * F γ * F γ₀ ≤ heightConst K n * F γ * (2 * F γ) := by gcongr
    _ = _ := by ring
