import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.SiegelParabolicBlocks

private theorem unip_shape {a b : ℕ} {R : Type} [CommRing R] (X : UPos (a + b) a → R) :
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks 1 ((unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ 0 (1 : Matrix (Fin b) (Fin b) R) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [unipMatrix, blockEntry_apply, Matrix.one_apply, Matrix.toBlocks₁₂, Fin.ext_iff] <;> omega

private theorem unip_fill {a b : ℕ} {R : Type} [CommRing R] (B : Matrix (Fin a) (Fin b) R) : ∃ X : UPos (a + b) a → R,
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks 1 B 0 (1 : Matrix (Fin b) (Fin b) R) := by
  refine ⟨fun p => Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 B 0 0) p.1.1 p.1.2, ?_⟩
  rw [unip_shape]
  congr 1
  ext i j
  have : (Fin.castAdd b i : Fin (a + b)) ≠ Fin.natAdd a j := by
    simp [Fin.ext_iff]; omega
  simp [unipMatrix, blockEntry_apply, Matrix.toBlocks₁₂, this]

private theorem split_low {R : Type} [CommRing R] (g : GL (Fin (2 + 2)) R)
    (h : (g.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (h' : (g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0) :
    ∃ (c d : GL (Fin 2) R), (c.val = (g.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ ∧
      c⁻¹.val = (g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁) ∧
      ∃ X : UPos (2 + 2) 2 → R, g = unipGL X * blk c d := by
  have e1 : g.val.submatrix finSumFinEquiv finSumFinEquiv * g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv =
      (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) := by
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  have hg : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R, g.val.submatrix finSumFinEquiv finSumFinEquiv = M →
      g.val = M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rintro _ rfl
    simp
  generalize g.val.submatrix finSumFinEquiv finSumFinEquiv = M at *
  generalize g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv = N at *
  have hM := (Matrix.fromBlocks_toBlocks M).symm
  rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks N, h, h', Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at e1
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e1
  obtain ⟨e1, -, -, e2⟩ := e1
  obtain ⟨X, hX⟩ := unip_fill (M.toBlocks₁₂ * N.toBlocks₂₂)
  refine ⟨⟨_, _, e1, mul_eq_one_comm.1 e1⟩, ⟨_, _, e2, mul_eq_one_comm.1 e2⟩, ⟨rfl, rfl⟩, X, Units.ext ?_⟩
  have hX' : unipMatrix X = (Matrix.fromBlocks 1 (M.toBlocks₁₂ * N.toBlocks₂₂) 0 1).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hX]; simp
  rw [Units.val_mul, coe_unipGL, hX', hg M rfl]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_assoc, mul_eq_one_comm.1 e2, Matrix.mul_one]
  rw [← h, ← hM]

variable {K : Type} [Field K] [NumberField K]

private theorem low_of_borel {b : AdelicGLn.AdelicGL K (2 + 2)} (hb : b ∈ adelicBorel) :
    (b.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
  ext i j
  refine mem_adelicBorel.1 hb ?_
  show finSumFinEquiv (Sum.inl j) < finSumFinEquiv (Sum.inr i)
  simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
  omega

private theorem hh_of (g : G1 K (2 + 2)) (X : UPos (2 + 2) 2 → 𝔸[K]) (a c : AdelicGLn.AdelicGL K 2)
    {k : AdelicGLn.AdelicGL K (2 + 2)} (hk : k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))))
    (e : (g : AdelicGLn.AdelicGL K (2 + 2)) = unipGL X * blk a c * k) :
    HH g = Real.log (detModule K 2 a).1 := by
  obtain ⟨hlv, -, -, -, hdet, -⟩ := blkLaws (K := K)
  have h1 : detModule K 2 a * detModule K 2 c = 1 := by
    have := mem_normOneGL_iff_detModule.1 g.2
    rwa [e, map_mul, map_mul, mem_normOneGL_iff_detModule.1 (unipGL_mem_normOneGL _), one_mul, hdet,
      mem_normOneGL_iff_detModule.1 (maxCompact_le_normOneGL hk), mul_one] at this
  let k' : G1 K (2 + 2) := ⟨k, maxCompact_le_normOneGL hk⟩
  have z1 : zt K (Real.log (detModule K 2 a).1) = centralSection K 2 (detModule K 2 a) := by
    unfold zt
    congr 1
    exact Subtype.ext (Real.exp_log (detModule K 2 a).2)
  have z2 : zt K (-Real.log (detModule K 2 a).1) = centralSection K 2 (detModule K 2 c) := by
    unfold zt
    congr 1
    refine Subtype.ext ?_
    rw [eq_inv_of_mul_eq_one_right h1]
    show Real.exp (-Real.log _) = _
    rw [Real.exp_neg, Real.exp_log (detModule K 2 a).2]
    rfl
  have e2 : g = nn X * lv (retractOne a) (retractOne c) (Real.log (detModule K 2 a).1) * k' := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hlv, z1, z2, coe_retractOne, coe_retractOne, inv_mul_cancel_right,
      inv_mul_cancel_right]
    exact e
  have hk' : k' ∈ KG K (2 + 2) := hk
  rw [e2, hpSpec.1, (hpSpec.2.1 k' hk').1, add_zero]

private theorem blk_diag {a b : ℕ} (ρ : Fin (a + b) → ℝ) (hρ : ∀ i, 0 < ρ i) :
    (diagUnits (a + b) fun i => posIdele (K := K) (ρ i) (hρ i)) =
      blk (diagUnits a fun i => posIdele (K := K) (ρ (Fin.castAdd b i)) (hρ _))
        (diagUnits b fun i => posIdele (K := K) (ρ (Fin.natAdd a i)) (hρ _)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blk, Matrix.diagonal_apply, Fin.ext_iff]

private theorem mod_diag {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    (detModule K n (diagUnits n fun i => posIdele (K := K) (r i) (hr i))).1 = (∏ i, r i) ^ Module.finrank ℚ K :=
  ideleModule_det_diagUnits_posIdele r hr

private theorem top_bound {ω : Set (AdelicGLn.AdelicGL K (2 + 2))} (h : Bor ω) :
    ∃ B : ℝ, ∀ b ∈ ω, ∃ (X : UPos (2 + 2) 2 → 𝔸[K]) (c d : AdelicGLn.AdelicGL K 2),
      b = unipGL X * blk c d ∧ |Real.log (detModule K 2 c).1| ≤ B := by
  obtain ⟨hc, hB⟩ := h
  have : CompactSpace ω := isCompact_iff_compactSpace.1 hc
  have hex : ∀ b : ω, _ := fun b : ω => split_low b.1 (low_of_borel (hB b.2)) (low_of_borel (inv_mem (hB b.2)))
  choose c d hc1 X hX using hex
  have c1 : Continuous fun b : ω => (b.1 : AdelicGLn.AdelicGL K (2 + 2)).val :=
    Units.continuous_val.comp continuous_subtype_val
  have c2 : Continuous fun b : ω => ((b.1 : AdelicGLn.AdelicGL K (2 + 2))⁻¹).val :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  have cc : Continuous c := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_matrix fun i j => ?_
      have e : (fun b : ω => (Units.val ∘ c) b i j) = fun b : ω =>
          (b.1 : AdelicGLn.AdelicGL K (2 + 2)).val (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) :=
        funext fun b => by simp only [Function.comp, (hc1 b).1]; rfl
      rw [e]
      exact c1.matrix_elem _ _
    · refine continuous_matrix fun i j => ?_
      have e : (fun b : ω => ((c b)⁻¹ : AdelicGLn.AdelicGL K 2).val i j) = fun b : ω =>
          ((b.1 : AdelicGLn.AdelicGL K (2 + 2))⁻¹).val (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) :=
        funext fun b => by simp only [(hc1 b).2]; rfl
      rw [e]
      exact c2.matrix_elem _ _
  have hf : Continuous fun b : ω => Real.log (detModule K 2 (c b)).1 :=
    (continuous_subtype_val.comp (continuous_detModule.comp cc)).log fun p => (detModule K 2 _).2.ne'
  obtain ⟨B, hB'⟩ := (isCompact_range hf.abs).bddAbove
  exact ⟨B, fun b hb => ⟨X ⟨b, hb⟩, c ⟨b, hb⟩, d ⟨b, hb⟩, hX ⟨b, hb⟩, hB' ⟨⟨b, hb⟩, rfl⟩⟩⟩

private theorem box (r : Fin (2 + 2) → ℝ) (hr : ∀ i, 0 < r i) {E R : ℝ} (hE : 1 ≤ E) (hR : 1 ≤ R)
    (hP : ∏ i, r i ≤ E) (hq : ∀ i j, r i / r j ≤ R) (i : Fin (2 + 2)) : r i ≤ E * R := by
  have hE0 : 0 < E := one_pos.trans_le hE
  have hR0 : 0 < R := one_pos.trans_le hR
  have hP0 : 0 < ∏ j, r j := Finset.prod_pos fun j _ => hr j
  have h1 : r i ^ (2 + 2) = (∏ j, r j) * ∏ j, (r i / r j) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    field_simp
  have h2 : ∏ j, (r i / r j) ≤ R ^ (2 + 2) := by
    calc ∏ j, (r i / r j) ≤ ∏ _j : Fin (2 + 2), R :=
          Finset.prod_le_prod (fun j _ => (div_pos (hr i) (hr j)).le) fun j _ => hq i j
      _ = R ^ (2 + 2) := by simp
  have h3 : r i ^ (2 + 2) ≤ (E * R) ^ (2 + 2) := by
    rw [h1, mul_pow]
    exact mul_le_mul (hP.trans (le_self_pow₀ hE (by norm_num))) h2
      (Finset.prod_pos fun j _ => div_pos (hr i) (hr j)).le (by positivity)
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h3

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.SiegelParabolicBlocks

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.SiegelParabolicBlocks in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.sgBasics :
    ∀ {K : Type} [Field K] [NumberField K] (ω : Set (AdelicGLn.AdelicGL K (2 + 2))), Bor ω → ∃ (C : ℝ) (c : ℕ), 1 ≤ C ∧ ∀ (ρ : Fin (2 + 2) → ℝ) (z : G1 K (2 + 2)), Sg ω ρ z →
      |HH z - (Module.finrank ℚ K : ℝ) * Real.log (ρ 0 * ρ 1)| ≤ C ∧ |Real.log (ρ 0 * ρ 1 * (ρ 2 * ρ 3))| ≤ C ∧
      ∀ R : ℝ, 1 ≤ R → (∀ i j, ρ i / ρ j ≤ R) → AutomorphicForm.height ((z : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ≤ C * R ^ c := by
  intro K _ _ ω hω
  obtain ⟨B₁, h₁⟩ := top_bound hω
  obtain ⟨p, q, hp, hpq, h₂⟩ := exists_pos_bounds hω.1 (f := fun b => (detModule K (2 + 2) b).1)
    (continuous_subtype_val.comp continuous_detModule) fun b _ => (detModule K (2 + 2) b).2
  obtain ⟨M, hM⟩ := exists_height_le_of_isCompact hω.1
  set B₂ := max |Real.log p| |Real.log q| with hB₂
  have hB₂0 : 0 ≤ B₂ := (abs_nonneg _).trans (le_max_left _ _)
  set E := Real.exp B₂ with hEdef
  have hE : 1 ≤ E := Real.one_le_exp hB₂0
  set e := 2 * Fintype.card (InfinitePlace K) with he
  set c := heightConst K (2 + 2) with hc
  have hc1 : 1 ≤ c := one_le_heightConst
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  refine ⟨max 1 (max B₁ (max B₂ (c * (c * M * E ^ e)))), e, le_max_left _ _, ?_⟩
  rintro ρ z ⟨hρ, b, hb, k, hk, e0⟩
  set C := max 1 (max B₁ (max B₂ (c * (c * M * E ^ e)))) with hC
  have C1 : B₁ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have C2 : B₂ ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have C3 : c * (c * M * E ^ e) ≤ C :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  set D := diagUnits (2 + 2) fun i => posIdele (K := K) (ρ i) (hρ i) with hD
  have hP0 : 0 < ∏ i, ρ i := Finset.prod_pos fun i _ => hρ i
  have hd1 : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hprod : ∏ i, ρ i = ρ 0 * ρ 1 * (ρ 2 * ρ 3) := by
    refine (Fin.prod_univ_four ρ).trans ?_
    ring

  have hm : (detModule K (2 + 2) b).1 * (∏ i, ρ i) ^ Module.finrank ℚ K = 1 := by
    have h := congrArg Subtype.val (mem_normOneGL_iff_detModule.1 z.2)
    rw [e0, map_mul, map_mul, mem_normOneGL_iff_detModule.1 (maxCompact_le_normOneGL hk), mul_one,
      Positive.val_mul, hD, mod_diag] at h
    exact h
  have hmpos := (detModule K (2 + 2) b).2
  have hlogm : |Real.log (detModule K (2 + 2) b).1| ≤ B₂ := by
    have l1 := Real.log_le_log hp (h₂ b hb).1
    have l2 := Real.log_le_log hmpos (h₂ b hb).2
    refine abs_le.2 ⟨?_, l2.trans ((le_abs_self _).trans (le_max_right _ _))⟩
    have := (neg_abs_le (Real.log p)).trans l1
    have h3 : |Real.log p| ≤ B₂ := le_max_left _ _
    linarith
  have hlogP : |Real.log (∏ i, ρ i)| ≤ B₂ := by
    have h := congrArg Real.log hm
    rw [Real.log_mul hmpos.ne' (pow_pos hP0 _).ne', Real.log_pow, Real.log_one] at h
    have h4 : (Module.finrank ℚ K : ℝ) * |Real.log (∏ i, ρ i)| = |Real.log (detModule K (2 + 2) b).1| := by
      have h5 : (Module.finrank ℚ K : ℝ) * Real.log (∏ i, ρ i) = -Real.log (detModule K (2 + 2) b).1 := by linarith
      rw [← abs_neg (Real.log (detModule K (2 + 2) b).1), ← h5, abs_mul, abs_of_pos (one_pos.trans_le hd1)]
    calc |Real.log (∏ i, ρ i)| ≤ (Module.finrank ℚ K : ℝ) * |Real.log (∏ i, ρ i)| :=
          le_mul_of_one_le_left (abs_nonneg _) hd1
      _ ≤ B₂ := h4.le.trans hlogm
  refine ⟨?_, by rw [← hprod]; exact hlogP.trans C2, fun R hR hq => ?_⟩
  · obtain ⟨X, a, a', hb', hbound⟩ := h₁ b hb
    have ez : (z : AdelicGLn.AdelicGL K (2 + 2)) = unipGL X *
        blk (a * diagUnits 2 fun i => posIdele (K := K) (ρ (Fin.castAdd 2 i)) (hρ _))
          (a' * diagUnits 2 fun i => posIdele (K := K) (ρ (Fin.natAdd 2 i)) (hρ _)) * k := by
      rw [e0, hb', hD, blk_diag, mul_assoc (unipGL X), (blkLaws (K := K)).2.2.2.2.2.1]
    have hH := hh_of z X _ _ hk ez
    have e01 : ∏ i : Fin 2, ρ (Fin.castAdd 2 i) = ρ 0 * ρ 1 := by
      rw [Fin.prod_univ_two]
      rfl
    rw [hH, map_mul, Positive.val_mul, mod_diag, Real.log_mul (detModule K 2 a).2.ne'
      (pow_pos (Finset.prod_pos fun i _ => hρ _) _).ne', Real.log_pow, e01, add_sub_cancel_right]
    exact hbound.trans C1
  · have hPle : ∏ i, ρ i ≤ E := by
      rw [← Real.log_le_iff_le_exp hP0]
      exact (le_abs_self _).trans hlogP
    have hPinv : ∏ i, (ρ i)⁻¹ ≤ E := by
      rw [Finset.prod_inv_distrib, ← Real.log_le_iff_le_exp (inv_pos.2 hP0), Real.log_inv]
      exact (neg_le_abs _).trans hlogP
    have hL1 : 1 ≤ E * R := one_le_mul_of_one_le_of_one_le hE hR
    have hbox : ∀ i, ρ i ≤ E * R ∧ (ρ i)⁻¹ ≤ E * R := fun i =>
      ⟨box ρ hρ hE hR hPle hq i, box (fun i => (ρ i)⁻¹) (fun i => inv_pos.2 (hρ i)) hE hR hPinv
        (fun i j => by rw [inv_div_inv]; exact hq j i) i⟩
    have hDh : AutomorphicForm.height D ≤ (E * R) ^ e := height_diagUnits_posIdele_le hρ hL1 hbox
    have hbM := hM b hb
    have hbpos := AutomorphicForm.height_pos b
    rw [e0]
    refine (AutomorphicForm.height_mul_le _ _).trans ?_
    rw [AutomorphicForm.height_eq_one_of_mem_maxCompact hk, mul_one]
    have h5 : AutomorphicForm.height (b * D) ≤ c * M * (E * R) ^ e :=
      (AutomorphicForm.height_mul_le _ _).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hbM hc0) hDh (AutomorphicForm.height_pos _).le
          (mul_nonneg hc0 (hbpos.le.trans hbM)))
    calc c * AutomorphicForm.height (b * D) ≤ c * (c * M * (E * R) ^ e) := mul_le_mul_of_nonneg_left h5 hc0
      _ = c * (c * M * E ^ e) * R ^ e := by rw [mul_pow]; ring
      _ ≤ C * R ^ e := mul_le_mul_of_nonneg_right C3 (by positivity)
