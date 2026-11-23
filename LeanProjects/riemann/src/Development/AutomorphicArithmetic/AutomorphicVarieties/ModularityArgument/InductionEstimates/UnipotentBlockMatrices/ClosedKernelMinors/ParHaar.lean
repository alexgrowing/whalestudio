import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdMeas
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
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

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.parHaar :
    ∀ {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure], ∃ (S : Subgroup (G1 K (2 + 2))) (ν : Measure S), IsClosed (S : Set (G1 K (2 + 2))) ∧ ν.IsHaarMeasure ∧
      (∀ g, g ∈ S ↔ ∃ X m₁ m₂ t, g = nn X * lv m₁ m₂ t) ∧ ∀ Φ : G1 K (2 + 2) → ℝ≥0∞, Measurable Φ →
        ∫⁻ s, Φ s ∂ν = ∫⁻ m₁, ∫⁻ m₂, ∫⁻ t : ℝ, ∫⁻ X, Φ (nn X * lv m₁ m₂ t) * ENNReal.ofReal (Real.exp (-4 * t)) ∂unipMeasure K (2 + 2) 2 ∂volume ∂μ₂ ∂μ₂ := by
  intro K _ _ μ₂ _
  obtain ⟨S, φ, hS, hmem, hφ⟩ := par_homeo (K := K)
  obtain ⟨-, hmul, -⟩ := blkLaws (K := K)
  have hw : Continuous fun t : ℝ => Real.exp (-4 * t) := by fun_prop
  have hwm : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-4 * t)) := hw.measurable.ennreal_ofReal
  let w : Measure ℝ := volume.withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))
  haveI : IsLocallyFiniteMeasure w := IsLocallyFiniteMeasure.withDensity_ofReal hw
  haveI : w.IsOpenPosMeasure := Measure.AbsolutelyContinuous.isOpenPosMeasure
    (withDensity_absolutelyContinuous' hwm.aemeasurable (Eventually.of_forall fun t => by
      simp [Real.exp_pos]))
  haveI : (unipMeasure K (2 + 2) 2).IsAddHaarMeasure := inferInstance
  let ρ := μ₂.prod (μ₂.prod (w.prod (unipMeasure K (2 + 2) 2)))
  have form : ∀ f : S → ℝ≥0∞, Measurable f → ∫⁻ s, f s ∂ρ.map φ = ∫⁻ m₁, ∫⁻ m₂, ∫⁻ t : ℝ, ∫⁻ X,
      f (φ (m₁, m₂, t, X)) * ENNReal.ofReal (Real.exp (-4 * t)) ∂unipMeasure K (2 + 2) 2 ∂volume ∂μ₂ ∂μ₂ := by
    intro f hf
    have hm : Measurable fun p => f (φ p) := hf.comp φ.continuous.measurable
    rw [lintegral_map hf φ.continuous.measurable, lintegral_prod _ hm.aemeasurable]
    refine lintegral_congr fun m₁ => ?_
    have hm1 : Measurable fun p => f (φ (m₁, p)) := hm.comp measurable_prodMk_left
    rw [lintegral_prod _ hm1.aemeasurable]
    refine lintegral_congr fun m₂ => ?_
    have hm2 : Measurable fun p => f (φ (m₁, m₂, p)) := hm1.comp measurable_prodMk_left
    rw [lintegral_prod _ hm2.aemeasurable, lintegral_withDensity_eq_lintegral_mul _ hwm hm2.lintegral_prod_right']
    refine lintegral_congr fun t => ?_
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, Pi.mul_apply, mul_comm]
  haveI : IsFiniteMeasureOnCompacts (ρ.map φ) := Measure.IsFiniteMeasureOnCompacts.map ρ φ
  haveI : (ρ.map φ).IsOpenPosMeasure := φ.continuous.isOpenPosMeasure_map φ.surjective
  haveI : (ρ.map φ).IsMulLeftInvariant := ⟨fun g => by
    obtain ⟨⟨a, b, u, Y⟩, rfl⟩ := φ.surjective g
    obtain ⟨e, he, hme⟩ := adMeas a b u
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    rw [lintegral_map hf (measurable_const_mul _), form f hf, form (fun s => f (φ (a, b, u, Y) * s)) (hf.comp (measurable_const_mul _))]
    have h1 : ∀ m₁ m₂ t X, φ (a, b, u, Y) * φ (m₁, m₂, t, X) = φ (a * m₁, b * m₂, u + t, Y + e.symm X) := by
      intro m₁ m₂ t X
      refine Subtype.ext ?_
      have := he (e.symm X)
      rw [e.apply_symm_apply] at this
      rw [Subgroup.coe_mul, hφ, hφ, hφ, mul_assoc, ← mul_assoc (lv a b u), ← this, mul_assoc, hmul, ← mul_assoc]
      exact congrArg (· * _) (unipOne_add 2 Y _).symm
    have h2 : ∀ (H : (UPos (2 + 2) 2 → 𝔸[K]) → ℝ≥0∞) (t : ℝ),
        ∫⁻ X, H (Y + e.symm X) * ENNReal.ofReal (Real.exp (-4 * t)) ∂unipMeasure K (2 + 2) 2 =
          ∫⁻ X, H X * ENNReal.ofReal (Real.exp (-4 * (u + t))) ∂unipMeasure K (2 + 2) 2 := by
      intro H t
      have h3 := lintegral_map_equiv (μ := unipMeasure K (2 + 2) 2) (fun X => H (Y + e.symm X))
        e.toHomeomorph.toMeasurableEquiv
      have h4 : (e.toHomeomorph.toMeasurableEquiv : _ → _) = e := rfl
      rw [h4, hme, lintegral_smul_measure] at h3
      simp only [e.symm_apply_apply, lintegral_add_left_eq_self, smul_eq_mul] at h3
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, ← h3,
        mul_right_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, mul_comm]
      congr 3
      ring
    simp only [h1]
    refine Eq.trans (lintegral_congr fun m₁ => ?_) (lintegral_mul_left_eq_self (μ := μ₂) _ a)
    refine Eq.trans (lintegral_congr fun m₂ => ?_) (lintegral_mul_left_eq_self (μ := μ₂) _ b)
    refine Eq.trans (lintegral_congr fun t => ?_) (lintegral_add_left_eq_self (μ := volume) _ u)
    exact h2 (fun X => f (φ (a * m₁, b * m₂, u + t, X))) t⟩
  refine ⟨S, ρ.map φ, hS, {}, hmem, fun Φ hΦ => ?_⟩
  rw [form (fun s => Φ s) (hΦ.comp measurable_subtype_coe)]
  simp only [hφ]
