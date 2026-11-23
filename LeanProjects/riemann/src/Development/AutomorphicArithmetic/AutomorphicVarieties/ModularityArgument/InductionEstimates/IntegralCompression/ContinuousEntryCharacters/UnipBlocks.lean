import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdMeas
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec

section MkAux

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate Valued
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem unip_blocks {a b : ℕ} {R : Type} [CommRing R] (X : UPos (a + b) a → R) :
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks 1 ((unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ 0 (1 : Matrix (Fin b) (Fin b) R) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [unipMatrix, blockEntry_apply, Matrix.one_apply, Matrix.toBlocks₁₂, Fin.ext_iff] <;> omega

private theorem unip_onto {a b : ℕ} {R : Type} [CommRing R] (B : Matrix (Fin a) (Fin b) R) : ∃ X : UPos (a + b) a → R,
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks 1 B 0 (1 : Matrix (Fin b) (Fin b) R) := by
  refine ⟨fun p => Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 B 0 0) p.1.1 p.1.2, ?_⟩
  rw [unip_blocks]
  congr 1
  ext i j
  have : (Fin.castAdd b i : Fin (a + b)) ≠ Fin.natAdd a j := by
    simp [Fin.ext_iff]; omega
  simp [unipMatrix, blockEntry_apply, Matrix.toBlocks₁₂, this]

private theorem low_zero {a b : ℕ} {R : Type} [CommRing R] (X : UPos (a + b) a → R) (c : GL (Fin a) R) (d : GL (Fin b) R) :
    ((unipGL X * blk c d).val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
  rw [Units.val_mul, ← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv, coe_unipGL, unip_blocks]
  simp [blk, Matrix.fromBlocks_multiply]

private theorem dec {a b : ℕ} {R : Type} [CommRing R] (g : GL (Fin (a + b)) R)
    (h : (g.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (h' : (g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0) :
    ∃ (c : GL (Fin a) R) (d : GL (Fin b) R), (c.val = (g.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ ∧
      c⁻¹.val = (g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁) ∧
      (d.val = (g.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ ∧
      d⁻¹.val = (g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂) ∧
      ∃ X : UPos (a + b) a → R, g = unipGL X * blk c d := by
  have e1 : g.val.submatrix finSumFinEquiv finSumFinEquiv * g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv =
      (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R) := by
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  have hg : ∀ M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R, g.val.submatrix finSumFinEquiv finSumFinEquiv = M →
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
  obtain ⟨X, hX⟩ := unip_onto (M.toBlocks₁₂ * N.toBlocks₂₂)
  refine ⟨⟨_, _, e1, mul_eq_one_comm.1 e1⟩, ⟨_, _, e2, mul_eq_one_comm.1 e2⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, X, Units.ext ?_⟩
  have hX' : unipMatrix X = (Matrix.fromBlocks 1 (M.toBlocks₁₂ * N.toBlocks₂₂) 0 1).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hX]; simp
  rw [Units.val_mul, coe_unipGL, hX', hg M rfl]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_assoc, mul_eq_one_comm.1 e2, Matrix.mul_one]
  rw [← h, ← hM]

private theorem low_coord {K : Type} [Field K] [NumberField K] :
    ∃ (C : Set (G1 K (2 + 2))) (ψ : C → G1 K 2 × G1 K 2 × ℝ × (UPos (2 + 2) 2 → 𝔸[K])), IsClosed C ∧ Continuous ψ ∧
      (∀ g : G1 K (2 + 2), (∃ X m₁ m₂ t, g = nn X * lv m₁ m₂ t) → (∃ X m₁ m₂ t, g⁻¹ = nn X * lv m₁ m₂ t) → g ∈ C) ∧
      ∀ s : C, (s : G1 K (2 + 2)) = nn (ψ s).2.2.2 * lv (ψ s).1 (ψ s).2.1 (ψ s).2.2.1 := by
  obtain ⟨hlv, -, -, hc, hdet, -⟩ := blkLaws (K := K)
  let F : G1 K (2 + 2) → Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) 𝔸[K] := fun g =>
    (g : AdelicGLn.AdelicGL K (2 + 2)).val.submatrix finSumFinEquiv finSumFinEquiv
  have hF : Continuous F := (Units.continuous_val.comp continuous_subtype_val).matrix_submatrix _ _
  have hF' : Continuous fun g => F g⁻¹ := hF.comp continuous_inv
  let C : Set (G1 K (2 + 2)) := {g | (F g).toBlocks₂₁ = 0 ∧ (F g⁻¹).toBlocks₂₁ = 0}
  have hC : IsClosed C := (isClosed_eq (hF.matrix_submatrix Sum.inr Sum.inl) continuous_const).inter
    (isClosed_eq (hF'.matrix_submatrix Sum.inr Sum.inl) continuous_const)
  choose a d ha hd X hX using fun s : C => dec (s.1 : AdelicGLn.AdelicGL K (2 + 2)) s.2.1 s.2.2
  have hac : Continuous a := Units.continuous_iff.2
    ⟨((hF.matrix_submatrix Sum.inl Sum.inl).comp continuous_subtype_val).congr fun s => (ha s).1.symm,
      ((hF'.matrix_submatrix Sum.inl Sum.inl).comp continuous_subtype_val).congr fun s => (ha s).2.symm⟩
  have hdc : Continuous d := Units.continuous_iff.2
    ⟨((hF.matrix_submatrix Sum.inr Sum.inr).comp continuous_subtype_val).congr fun s => (hd s).1.symm,
      ((hF'.matrix_submatrix Sum.inr Sum.inr).comp continuous_subtype_val).congr fun s => (hd s).2.symm⟩
  let t : C → ℝ := fun s => Real.log (detModule K 2 (a s)).1
  have htc : Continuous t :=
    (continuous_subtype_val.comp (continuous_detModule.comp hac)).log fun s => (detModule K 2 (a s)).2.ne'
  have key : ∀ s : C, (s : G1 K (2 + 2)) = nn (X s) * lv (retractOne (a s)) (retractOne (d s)) (t s) := by
    intro s
    have h1 : detModule K 2 (a s) * detModule K 2 (d s) = 1 := by
      have := mem_normOneGL_iff_detModule.1 s.1.2
      rwa [hX s, map_mul, mem_normOneGL_iff_detModule.1 (unipGL_mem_normOneGL _), one_mul, hdet] at this
    have z1 : zt K (t s) = centralSection K 2 (detModule K 2 (a s)) := by
      unfold zt
      congr 1
      exact Subtype.ext (Real.exp_log (detModule K 2 (a s)).2)
    have z2 : zt K (-t s) = centralSection K 2 (detModule K 2 (d s)) := by
      unfold zt
      congr 1
      refine Subtype.ext ?_
      rw [eq_inv_of_mul_eq_one_right h1]
      show Real.exp (-Real.log _) = _
      rw [Real.exp_neg, Real.exp_log (detModule K 2 (a s)).2]
      rfl
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, hlv, z1, z2, coe_retractOne, coe_retractOne, inv_mul_cancel_right, inv_mul_cancel_right]
    exact hX s
  have hP : Continuous fun s : C => (retractOne (a s), retractOne (d s), t s) :=
    (continuous_retractOne.comp hac).prodMk ((continuous_retractOne.comp hdc).prodMk htc)
  have hL : Continuous fun s : C => lv (retractOne (a s)) (retractOne (d s)) (t s) := by
    simpa only [Function.comp_def] using hc.comp hP
  have hN : Continuous fun s : C => unipMatrix (X s) := by
    have : Continuous fun s : C => (nn (X s) : G1 K (2 + 2)) :=
      (continuous_subtype_val.mul hL.inv).congr fun s => mul_inv_eq_of_eq_mul (key s)
    have h2 : Continuous fun g : G1 K (2 + 2) => (g : AdelicGLn.AdelicGL K (2 + 2)).val :=
      Units.continuous_val.comp continuous_subtype_val
    exact h2.comp this
  have hXc : Continuous X := continuous_pi fun p => by
    refine ((hN.matrix_elem p.1.1 p.1.2).sub (continuous_const (y := (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) p.1.1 p.1.2))).congr fun s => ?_
    show unipMatrix (X s) p.1.1 p.1.2 - _ = _
    rw [unipMatrix, Matrix.add_apply, blockEntry_apply, dif_pos p.2, add_sub_cancel_left]
  have hlow : ∀ g : G1 K (2 + 2), (∃ X m₁ m₂ t, g = nn X * lv m₁ m₂ t) → (F g).toBlocks₂₁ = 0 := by
    rintro _ ⟨X, m₁, m₂, t, rfl⟩
    simp only [F, Subgroup.coe_mul, hlv]
    exact low_zero _ _ _
  exact ⟨C, fun s => (retractOne (a s), retractOne (d s), t s, X s), hC,
    (continuous_retractOne.comp hac).prodMk ((continuous_retractOne.comp hdc).prodMk (htc.prodMk hXc)),
    fun g h h' => ⟨hlow _ h, hlow _ h'⟩, key⟩

private theorem par_homeo {K : Type} [Field K] [NumberField K] :
    ∃ (S : Subgroup (G1 K (2 + 2))) (φ : (G1 K 2 × G1 K 2 × ℝ × (UPos (2 + 2) 2 → 𝔸[K])) ≃ₜ S),
      IsClosed (S : Set (G1 K (2 + 2))) ∧ (∀ g, g ∈ S ↔ ∃ X m₁ m₂ t, g = nn X * lv m₁ m₂ t) ∧
      ∀ m₁ m₂ t X, (φ (m₁, m₂, t, X) : G1 K (2 + 2)) = nn X * lv m₁ m₂ t := by
  obtain ⟨-, hmul, hone, hc, -⟩ := blkLaws (K := K)
  obtain ⟨-, -, hinj, -⟩ := pkLaws (K := K)
  obtain ⟨C, ψ, hC, hψ, hin, hkey⟩ := low_coord (K := K)
  have hcomm : ∀ (m₁ m₂ : G1 K 2) (t : ℝ) X, ∃ Y, lv m₁ m₂ t * nn X = nn Y * lv m₁ m₂ t := by
    intro m₁ m₂ t X
    obtain ⟨e, he, -⟩ := adMeas m₁ m₂ t
    exact ⟨e.symm X, by rw [he, e.apply_symm_apply]⟩
  let S : Subgroup (G1 K (2 + 2)) :=
    { carrier := {g | ∃ X m₁ m₂ t, g = nn X * lv m₁ m₂ t}
      one_mem' := ⟨0, 1, 1, 0, by rw [hone, mul_one]; exact (unipOne_zero 2).symm⟩
      mul_mem' := by
        rintro _ _ ⟨X, m₁, m₂, t, rfl⟩ ⟨X', m₁', m₂', t', rfl⟩
        obtain ⟨Y, hY⟩ := hcomm m₁ m₂ t X'
        refine ⟨X + Y, m₁ * m₁', m₂ * m₂', t + t', ?_⟩
        rw [mul_assoc, ← mul_assoc (lv m₁ m₂ t), hY, mul_assoc, hmul, ← mul_assoc]
        exact congrArg (· * _) (unipOne_add 2 X Y).symm
      inv_mem' := by
        rintro _ ⟨X, m₁, m₂, t, rfl⟩
        obtain ⟨Y, hY⟩ := hcomm m₁⁻¹ m₂⁻¹ (-t) (-X)
        refine ⟨Y, m₁⁻¹, m₂⁻¹, -t, ?_⟩
        rw [← hY, mul_inv_rev]
        congr 1
        · refine inv_eq_of_mul_eq_one_right ?_
          rw [hmul, mul_inv_cancel, mul_inv_cancel, add_neg_cancel, hone]
        · refine inv_eq_of_mul_eq_one_right ?_
          rw [← unipOne_add, add_neg_cancel, unipOne_zero] }
  have hSC : ∀ g ∈ S, g ∈ C := fun g hg => hin g hg (S.inv_mem hg)
  have hS : (S : Set (G1 K (2 + 2))) = C :=
    Set.Subset.antisymm hSC fun g hg => ⟨_, _, _, _, hkey ⟨g, hg⟩⟩
  have hL : Continuous fun p : G1 K 2 × G1 K 2 × ℝ × (UPos (2 + 2) 2 → 𝔸[K]) => lv p.1 p.2.1 p.2.2.1 := by
    have : Continuous fun p : G1 K 2 × G1 K 2 × ℝ × (UPos (2 + 2) 2 → 𝔸[K]) => (p.1, p.2.1, p.2.2.1) := by fun_prop
    simpa only [Function.comp_def] using hc.comp this
  have hN : Continuous fun p : G1 K 2 × G1 K 2 × ℝ × (UPos (2 + 2) 2 → 𝔸[K]) => (nn p.2.2.2 : G1 K (2 + 2)) :=
    (continuous_unipOne 2).comp (by fun_prop)
  refine ⟨S,
    { toFun := fun p => ⟨nn p.2.2.2 * lv p.1 p.2.1 p.2.2.1, _, _, _, _, rfl⟩
      invFun := fun s => ψ ⟨s.1, hSC _ s.2⟩
      left_inv := fun p => ?_
      right_inv := fun s => Subtype.ext (hkey ⟨s.1, hSC _ s.2⟩).symm
      continuous_toFun := (hN.mul hL).subtype_mk _
      continuous_invFun := hψ.comp (continuous_subtype_val.subtype_mk _) }, hS ▸ hC, fun _ => Iff.rfl, fun _ _ _ _ => rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := hinj _ _ _ _ _ _ _ _ (hkey ⟨_, hSC _ ⟨p.2.2.2, p.1, p.2.1, p.2.2.1, rfl⟩⟩)
  exact Prod.ext h2.symm (Prod.ext h3.symm (Prod.ext h4.symm h1.symm))

private def sumv {E : Type} [Zero E] (y₁ y₂ : Fin 2 → E) : Fin (2 + 2) → E :=
  fun i => Sum.elim y₁ y₂ (finSumFinEquiv.symm i)

private theorem sumv_mul {E : Type} [CommRing E] (A B D : Matrix (Fin 2) (Fin 2) E) (y₁ y₂ : Fin 2 → E) :
    Matrix.vecMul (sumv y₁ y₂) (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B 0 D)) =
      sumv (Matrix.vecMul y₁ A) (Matrix.vecMul y₁ B + Matrix.vecMul y₂ D) := by
  ext j
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective j
  simp only [Matrix.vecMul, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply, sumv, Equiv.symm_apply_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  rcases j with j | j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private theorem sumv_norm {E : Type} [NormedField E] (y₁ y₂ : Fin 2 → E) :
    euclidNorm (sumv y₁ y₂) ^ 2 = euclidNorm y₁ ^ 2 + euclidNorm y₂ ^ 2 := by
  rw [euclidNorm_sq, euclidNorm_sq, euclidNorm_sq, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp [sumv]

private theorem arch_contr {E : Type} [NormedField E] {A B D : Matrix (Fin 2) (Fin 2) E}
    (h : ∀ y, euclidNorm (Matrix.vecMul y (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B 0 D))) = euclidNorm y)
    (y : Fin 2 → E) : euclidNorm (Matrix.vecMul y A) ≤ euclidNorm y := by
  have h1 := congrArg (· ^ 2) (h (sumv y 0))
  simp only [sumv_mul, sumv_norm, Matrix.zero_vecMul, add_zero] at h1
  have h0 : euclidNorm (0 : Fin 2 → E) = 0 := by simp [euclidNorm]
  rw [h0] at h1
  have h2 : 0 ≤ euclidNorm (Matrix.vecMul y B) ^ 2 := by positivity
  refine abs_le_of_sq_le_sq' ?_ (euclidNorm_nonneg _) |>.2
  nlinarith

private theorem arch_low {E : Type} [NormedField E] {A B D : Matrix (Fin 2) (Fin 2) E}
    (h : ∀ y, euclidNorm (Matrix.vecMul y (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B 0 D))) = euclidNorm y)
    (y : Fin 2 → E) : euclidNorm (Matrix.vecMul y D) = euclidNorm y := by
  have h1 := congrArg (· ^ 2) (h (sumv 0 y))
  simp only [sumv_mul, sumv_norm, Matrix.zero_vecMul, zero_add] at h1
  have h0 : euclidNorm (0 : Fin 2 → E) = 0 := by simp [euclidNorm]
  rw [h0] at h1
  have h2 : euclidNorm (Matrix.vecMul y D) ^ 2 = euclidNorm y ^ 2 := by linarith
  exact (sq_eq_sq₀ (euclidNorm_nonneg _) (euclidNorm_nonneg _)).1 h2

private theorem arch_top {E : Type} [NormedField E] {A A' B B' D D' : Matrix (Fin 2) (Fin 2) E} (hA : A * A' = 1)
    (h : ∀ y, euclidNorm (Matrix.vecMul y (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B 0 D))) = euclidNorm y)
    (h' : ∀ y, euclidNorm (Matrix.vecMul y (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A' B' 0 D'))) = euclidNorm y)
    (y : Fin 2 → E) : euclidNorm (Matrix.vecMul y A) = euclidNorm y := by
  refine le_antisymm (arch_contr h y) ?_
  have := arch_contr h' (Matrix.vecMul y A)
  rwa [Matrix.vecMul_vecMul, hA, Matrix.vecMul_one] at this

private theorem ub_val {R : Type} [CommRing R] (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) :
    ∃ B B' : Matrix (Fin 2) (Fin 2) R,
      (unipGL X * blk a b).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a.val B 0 b.val) ∧
      ((unipGL X * blk a b)⁻¹).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (a⁻¹).val B' 0 (b⁻¹).val) := by
  have hU : ∀ X : UPos (2 + 2) 2 → R, ∃ B, unipMatrix X = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 B 0 1) := by
    intro X
    refine ⟨((unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂, ?_⟩
    rw [Matrix.reindex_apply, ← unip_blocks (a := 2) (b := 2) X]
    simp
  obtain ⟨B₀, h₀⟩ := hU X
  obtain ⟨B₁, h₁⟩ := hU (-X)
  refine ⟨B₀ * b.val, (a⁻¹).val * B₁, ?_, ?_⟩
  · rw [Units.val_mul, coe_unipGL, h₀]
    simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.one_mul,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  · rw [mul_inv_rev, Units.val_mul, coe_unipGL_inv, h₁]
    have hb : (blk a b)⁻¹ = blk a⁻¹ b⁻¹ := Units.ext rfl
    rw [hb]
    simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_one,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

private theorem map_blocks {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (A B D : Matrix (Fin 2) (Fin 2) R) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B 0 D)).map f =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (A.map f) (B.map f) 0 (D.map f)) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

private theorem kg_blocks {K : Type} [Field K] [NumberField K] {X : UPos (2 + 2) 2 → 𝔸[K]} {a b : AdelicGLn.AdelicGL K 2}
    (h : unipGL X * blk a b ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2)))) :
    a ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K 2)) ∧ b ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K 2)) := by
  obtain ⟨B, B', hB, hB'⟩ := ub_val X a b
  have hi := (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))).inv_mem h
  generalize unipGL X * blk a b = g at *
  have iv : ∀ {m : ℕ} (w : InfinitePlace K) (x : AdelicGLn.AdelicGL K m), (infAt w x).val = x.val.map (infEval w) :=
    fun w x => Matrix.ext fun i j => rfl
  have A1 : ∀ w y, euclidNorm (Matrix.vecMul y (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (a.val.map (infEval w)) (B.map (infEval w)) 0 (b.val.map (infEval w))))) = euclidNorm y := by
    intro w y
    have := (h.1 w) y
    rwa [iv, hB, map_blocks] at this
  have A2 : ∀ w y, euclidNorm (Matrix.vecMul y (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks ((a⁻¹).val.map (infEval w)) (B'.map (infEval w)) 0 ((b⁻¹).val.map (infEval w))))) = euclidNorm y := by
    intro w y
    have := (hi.1 w) y
    rwa [iv, hB', map_blocks] at this
  have T : ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (G : AdelicGLn.AdelicGL K (2 + 2)) (A : AdelicGLn.AdelicGL K 2) (p : Fin 2 → Fin (2 + 2)),
      (∀ i j, G.val (p i) (p j) = A.val i j) → (∀ i j, finAt v G i j ∈ (ValuativeRel.valuation (v.adicCompletion K)).integer) →
        ∀ i j, finAt v A i j ∈ (ValuativeRel.valuation (v.adicCompletion K)).integer := by
    intro v G A p hp h i j
    have := h (p i) (p j)
    rw [finAt_apply] at this ⊢
    rwa [show G (p i) (p j) = A i j from hp i j] at this
  have fin : ∀ (A : AdelicGLn.AdelicGL K 2) (p : Fin 2 → Fin (2 + 2)), (∀ i j, g.val (p i) (p j) = A.val i j) →
      (∀ i j, (g⁻¹).val (p i) (p j) = (A⁻¹).val i j) → ∀ v, finAt v A ∈ GLnLocal.integralGL (v.adicCompletion K) 2 := by
    intro A p h1 h2 v
    have e := (GLnLocal.mem_integralGL_iff _ _).1 (h.2 v)
    have e' := (GLnLocal.mem_integralGL_iff _ _).1 (hi.2 v)
    refine (GLnLocal.mem_integralGL_iff _ _).2 ⟨T v g A p h1 e.1, ?_⟩
    rw [← finAt_inv]
    exact T v g⁻¹ A⁻¹ p h2 e'.1
  refine ⟨⟨fun w => ?_, fin a (fun i => finSumFinEquiv (Sum.inl i)) ?_ ?_⟩, ⟨fun w => ?_, fin b (fun i => finSumFinEquiv (Sum.inr i)) ?_ ?_⟩⟩
  · refine mem_archCompact.2 fun y => ?_
    rw [iv]
    refine arch_top ?_ (A1 w) (A2 w) y
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  · intro i j; rw [hB]; simp
  · intro i j; rw [hB']; simp
  · refine mem_archCompact.2 fun y => ?_
    rw [iv]
    exact arch_low (A1 w) y
  · intro i j; rw [hB]; simp
  · intro i j; rw [hB']; simp

end MkAux

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.mkSec :
    ∀ (K : Type) [Field K] [NumberField K] (Λ : G1 K 2 → G1 K 2 → G1 K (2 + 2) → ℂ), Continuous (fun p : G1 K 2 × G1 K 2 × KG K (2 + 2) => Λ p.1 p.2.1 p.2.2) →
      (∀ m₁ m₂, ∀ u₁ ∈ KG K 2, ∀ u₂ ∈ KG K 2, ∀ k ∈ KG K (2 + 2), Λ (m₁ * u₁) (m₂ * u₂) k = Λ m₁ m₂ (lv u₁ u₂ 0 * k)) →
      (∀ m₁ m₂ X, nn X ∈ KG K (2 + 2) → ∀ k ∈ KG K (2 + 2), Λ m₁ m₂ (nn X * k) = Λ m₁ m₂ k) →
      ∃ f : G1 K (2 + 2) → ℂ, Continuous f ∧ ∀ X m₁ m₂ t, ∀ k ∈ KG K (2 + 2), f (nn X * lv m₁ m₂ t * k) = Λ m₁ m₂ k := by
  intro K _ _ Λ hΛ h2 h3
  obtain ⟨S, φ, hS, hmem, hφ⟩ := par_homeo (K := K)
  obtain ⟨hlv, hmul, hone, -, -, -, -, -, -, -, hlvK, hcpt⟩ := blkLaws (K := K)
  obtain ⟨-, -, hinj, -⟩ := pkLaws (K := K)
  obtain ⟨hH1, hH2, -⟩ := hpSpec (K := K)
  have hK : IsCompact (KG K (2 + 2) : Set (G1 K (2 + 2))) := (hcpt _).1
  have hsurj : Function.Surjective (HaarSK.mulMap S (KG K (2 + 2))) := by
    intro g
    obtain ⟨X, m₁, m₂, t, k, hk, rfl⟩ := iwa g
    exact ⟨(φ (m₁, m₂, t, X), ⟨k, hk⟩), by simp [HaarSK.mulMap, hφ]⟩
  have hq := HaarSK.isQuotientMap_mulMap hS hK hsurj
  let F : S × KG K (2 + 2) → ℂ := fun p => Λ (φ.symm p.1).1 (φ.symm p.1).2.1 p.2
  have hF : Continuous F := by
    have h1 : Continuous fun p : S × KG K (2 + 2) => ((φ.symm p.1).1, (φ.symm p.1).2.1, p.2) := by
      have := φ.symm.continuous
      fun_prop
    exact hΛ.comp h1
  have hnn : ∀ Y : UPos (2 + 2) 2 → 𝔸[K], (nn Y)⁻¹ = nn (-Y) := by
    intro Y
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← unipOne_add, add_neg_cancel, unipOne_zero]
  have hconst : ∀ p p', HaarSK.mulMap S (KG K (2 + 2)) p = HaarSK.mulMap S (KG K (2 + 2)) p' → F p = F p' := by
    rintro ⟨s, k⟩ ⟨s', k'⟩ hp
    obtain ⟨⟨m₁, m₂, t, X⟩, rfl⟩ := φ.surjective s
    obtain ⟨⟨m₁', m₂', t', X'⟩, rfl⟩ := φ.surjective s'
    simp only [HaarSK.mulMap, hφ] at hp
    simp only [F, Homeomorph.symm_apply_apply]

    have hκS : ((φ (m₁, m₂, t, X) : G1 K (2 + 2)))⁻¹ * (φ (m₁', m₂', t', X') : G1 K (2 + 2)) ∈ S :=
      S.mul_mem (S.inv_mem (φ _).2) (φ _).2
    have hκe : ((φ (m₁, m₂, t, X) : G1 K (2 + 2)))⁻¹ * (φ (m₁', m₂', t', X') : G1 K (2 + 2)) = (k : G1 K (2 + 2)) * (k' : G1 K (2 + 2))⁻¹ := by
      rw [hφ, hφ, inv_mul_eq_iff_eq_mul, ← mul_assoc, hp, mul_inv_cancel_right]
    obtain ⟨Y, a, b, u, hκ⟩ := (hmem _).1 hκS
    have hκK : (k : G1 K (2 + 2)) * (k' : G1 K (2 + 2))⁻¹ ∈ KG K (2 + 2) := (KG K (2 + 2)).mul_mem k.2 ((KG K (2 + 2)).inv_mem k'.2)
    rw [hκe] at hκ
    have hu : u = 0 := by
      have e1 := (hH2 _ hκK).1
      have e2 := hH1 Y a b u 1
      rw [mul_one, ← hκ, e1, (hH2 1 (KG K (2 + 2)).one_mem).1] at e2
      linarith
    subst hu
    have hzt : zt K 0 = 1 := by
      rw [zt, ← map_one (centralSection K 2)]
      exact congrArg _ (Subtype.ext Real.exp_zero)
    have hcoe : ((k : G1 K (2 + 2)) * (k' : G1 K (2 + 2))⁻¹ : G1 K (2 + 2)).1 = unipGL Y * blk a.1 b.1 := by
      rw [hκ, Subgroup.coe_mul, hlv, neg_zero, hzt, mul_one, mul_one, coe_unipOne]
    have hab := kg_blocks (hcoe ▸ hκK : unipGL Y * blk a.1 b.1 ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))))
    have ha : a ∈ KG K 2 := hab.1
    have hb : b ∈ KG K 2 := hab.2
    have hl := hlvK a ha b hb
    have hnY : nn (-Y) ∈ KG K (2 + 2) := by
      rw [← hnn]
      refine (KG K (2 + 2)).inv_mem ?_
      have : nn Y = (k : G1 K (2 + 2)) * (k' : G1 K (2 + 2))⁻¹ * (lv a b 0)⁻¹ := by rw [hκ, mul_inv_cancel_right]
      rw [this]
      exact (KG K (2 + 2)).mul_mem hκK ((KG K (2 + 2)).inv_mem hl)

    obtain ⟨e, he, -⟩ := adMeas m₁ m₂ t
    have hs' : nn X' * lv m₁' m₂' t' = nn (X + e.symm Y) * lv (m₁ * a) (m₂ * b) (t + 0) := by
      have h1 : nn X' * lv m₁' m₂' t' = nn X * lv m₁ m₂ t * (nn Y * lv a b 0) := by
        rw [← hκ, ← hκe, hφ, hφ, mul_inv_cancel_left]
      have h4 := he (e.symm Y)
      rw [e.apply_symm_apply] at h4
      have hadd : nn (X + e.symm Y) = nn X * nn (e.symm Y) := unipOne_add 2 X _
      rw [h1, ← hmul, hadd]
      simp only [mul_assoc]
      rw [← mul_assoc (nn (e.symm Y)), h4]
      simp only [mul_assoc]
    obtain ⟨-, e1, e2, -⟩ := hinj _ _ _ _ _ _ _ _ hs'
    subst e1 e2
    show Λ m₁ m₂ k = Λ (m₁ * a) (m₂ * b) k'
    rw [h2 m₁ m₂ a ha b hb k' k'.2]
    have h5 : lv a b 0 * (k' : G1 K (2 + 2)) = nn (-Y) * k := by
      rw [← hnn, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hκ, inv_mul_cancel_right]
    rw [h5, h3 m₁ m₂ (-Y) hnY k k.2]
  refine ⟨fun g => F (Function.surjInv hsurj g), ?_, ?_⟩
  · refine hq.continuous_iff.2 ?_
    refine hF.congr fun p => ?_
    exact hconst _ _ (Function.surjInv_eq hsurj _).symm
  · intro X m₁ m₂ t k hk
    have h1 : nn X * lv m₁ m₂ t * k = HaarSK.mulMap S (KG K (2 + 2)) (φ (m₁, m₂, t, X), ⟨k, hk⟩) := by
      simp [HaarSK.mulMap, hφ]
    show F _ = _
    rw [hconst _ (φ (m₁, m₂, t, X), ⟨k, hk⟩) (by rw [Function.surjInv_eq hsurj, h1])]
    simp [F]
