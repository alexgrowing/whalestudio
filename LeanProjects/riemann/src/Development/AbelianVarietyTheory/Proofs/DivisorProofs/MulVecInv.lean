import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecLineOneLeVecLine
open scoped TensorProduct NNReal ENNReal Matrix ComplexConjugate
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.StdPar GlobalTheory.EisUnfold
open GlobalTheory.Doubling (absE)
open GlobalTheory.EisMidHt (adVec)
open Matrix

noncomputable section

namespace GlobalTheory.FlagNorm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in
theorem mulVec_inv (g : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J g).1 *ᵥ (matHom _ σ J g⁻¹).1 *ᵥ y = y := by
  rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mulVec]

omit [NumberField E] in
theorem inv_mulVec (g : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J g⁻¹).1 *ᵥ (matHom _ σ J g).1 *ᵥ y = y := by
  rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]

omit [NumberField E] in
theorem keep_inv {g : GAd σ J} {A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)}
    (hA : ∀ y, y ∈ A ↔ (matHom _ σ J g).1 *ᵥ y ∈ A) (y : Fin n → AF F ⊗[F] E) :
    y ∈ A ↔ (matHom _ σ J g⁻¹).1 *ᵥ y ∈ A := by
  rw [hA ((matHom _ σ J g⁻¹).1 *ᵥ y), mulVec_inv]

omit [NumberField E] in
theorem conj_mulVec (m u : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y =
      (matHom _ σ J m).1 *ᵥ (matHom _ σ J u).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y := by
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]

omit [NumberField E] in
theorem conj_sub (m u : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y - y =
      (matHom _ σ J m).1 *ᵥ ((matHom _ σ J u).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y - (matHom _ σ J m⁻¹).1 *ᵥ y) := by
  rw [conj_mulVec, mulVec_sub, mulVec_inv]

omit [NumberField E] in
theorem keep_conj {m u : GAd σ J} {A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)}
    (hm : ∀ y, y ∈ A ↔ (matHom _ σ J m).1 *ᵥ y ∈ A) (hu : ∀ y, y ∈ A ↔ (matHom _ σ J u).1 *ᵥ y ∈ A)
    (y : Fin n → AF F ⊗[F] E) : y ∈ A ↔ (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y ∈ A := by
  rw [conj_mulVec]
  exact (keep_inv hm y).trans ((hu _).trans (hm _))

theorem perp_inv {X : Matrix (Fin n) (Fin r) E} {k : Fin r} {g : GAd σ J}
    (hg : ∀ y, y ∈ colSpan F X {i | i ≤ k} ↔ (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X {i | i ≤ k})
    {y : Fin n → AF F ⊗[F] E} (hy : y ∈ colPerp σ J X {i | i ≤ k}) :
    (matHom _ σ J g⁻¹).1 *ᵥ y ∈ colPerp σ J X {i | i ≤ k} := by
  have hcol : ∀ i : Fin (k.val + 1), (matHom _ σ J g).1 *ᵥ (fun l => adMat F (initCols X k) l i) ∈
      colSpan F X {i | i ≤ k} := fun i =>
    (hg _).1 (Submodule.subset_span ⟨i.castLE k.2, Nat.le_of_lt_succ i.2, rfl⟩)
  choose a ha using fun i => mem_colSpan_iff.1 (hcol i)
  have hB : (matHom _ σ J g).1 * adMat F (initCols X k) = adMat F (initCols X k) * Matrix.of (fun l i => a i l) :=
    Matrix.ext fun l i => (congrFun (ha i) l).symm
  have hF := GlobalTheory.UAut.form_mul_of_mul_cols hB
  rw [mem_colPerp_iff] at hy ⊢
  rw [mulVec_mulVec, hF, ← mulVec_mulVec, hy, mulVec_zero]

end GlobalTheory.FlagNorm

open GlobalTheory.FlagNorm in

theorem GlobalTheory.FlagNorm.conj_mem_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
    ∀ (T : Finset (Fin r)) (m : GAd σ J),
      (∀ k ∈ T, ∀ y, y ∈ colSpan F X {i | i ≤ k} ↔ (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | i ≤ k}) →
      ∀ u ∈ unip σ J X T, m * u * m⁻¹ ∈ unip σ J X T := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW T m hm u hu
  by_cases hT : T = ∅
  · subst hT
    rw [unip_empty, Subgroup.mem_bot] at hu ⊢
    simp [hu]
  have hne := Finset.nonempty_iff_ne_empty.2 hT
  have hkMT : T.max' hne ∈ T := T.max'_mem _
  have eB : {i | ∃ k ∈ T, i ≤ k} = {i | i ≤ T.max' hne} :=
    Set.ext fun i => ⟨fun ⟨k, hk, hik⟩ => hik.trans (T.le_max' k hk), fun hi => ⟨_, hkMT, hi⟩⟩

  have keepSub : ∀ T' : Finset (Fin r), T' ⊆ T → ∀ y, y ∈ colSpan F X {i | ∃ k ∈ T', i ≤ k} ↔
      (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | ∃ k ∈ T', i ≤ k} := by
    intro T' hT' y
    by_cases h0 : T' = ∅
    · subst h0
      have e : {i : Fin r | ∃ k ∈ (∅ : Finset (Fin r)), i ≤ k} = ∅ := by simp
      rw [e, colSpan, Set.image_empty, Submodule.span_empty, Submodule.mem_bot, Submodule.mem_bot]
      exact ⟨fun hy => by rw [hy, mulVec_zero], fun hy => by rw [← inv_mulVec m y, hy, mulVec_zero]⟩
    · have hne' := Finset.nonempty_iff_ne_empty.2 h0
      have e : {i | ∃ k ∈ T', i ≤ k} = {i | i ≤ T'.max' hne'} :=
        Set.ext fun i => ⟨fun ⟨k, hk, hik⟩ => hik.trans (T'.le_max' k hk), fun hi => ⟨_, T'.max'_mem _, hi⟩⟩
      rw [e]
      exact hm _ (hT' (T'.max'_mem _)) y
  have eA : ∀ j : Fin r, {i | ∃ k ∈ T, i ≤ k ∧ k < j} = {i | ∃ k ∈ T.filter (· < j), i ≤ k} := fun j =>
    Set.ext fun i => ⟨fun ⟨k, hk, h1, h2⟩ => ⟨k, Finset.mem_filter.2 ⟨hk, h2⟩, h1⟩,
      fun ⟨k, hk, h1⟩ => ⟨k, (Finset.mem_filter.1 hk).1, h1, (Finset.mem_filter.1 hk).2⟩⟩
  have keepA : ∀ j : Fin r, ∀ y, y ∈ colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} ↔
      (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} := fun j => by
    rw [eA j]
    exact keepSub _ (Finset.filter_subset _ _)
  have keepB := keepSub T subset_rfl
  rw [eB] at keepB
  have hu1 : ∀ j, u ∈ trivOn σ J (colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j}) (colSpan F X {j}) :=
    fun j => Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hu).1 j
  have hu2 : u ∈ trivOn σ J (colSpan F X {i | i ≤ T.max' hne}) (colPerp σ J X {i | i ≤ T.max' hne}) := by
    have := (Subgroup.mem_inf.1 hu).2
    rw [eB] at this
    exact this
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun j => ⟨keep_conj (keepA j) (hu1 j).1, fun y hy => ?_⟩, ?_⟩
  ·
    unfold colSpan at hy
    rw [Set.image_singleton, Submodule.mem_span_singleton] at hy
    obtain ⟨a, rfl⟩ := hy
    rw [mulVec_smul, ← smul_sub]
    refine Submodule.smul_mem _ a ?_
    rw [conj_sub]
    refine (keepA j _).1 ?_
    set z := (matHom _ σ J m⁻¹).1 *ᵥ (adMat F X)ᵀ j
    by_cases hex : ∃ k ∈ T, j ≤ k
    · have hne2 : (T.filter (j ≤ ·)).Nonempty := let ⟨k, hk, hjk⟩ := hex; ⟨k, Finset.mem_filter.2 ⟨hk, hjk⟩⟩
      set k0 := (T.filter (j ≤ ·)).min' hne2
      have hk0 := Finset.mem_filter.1 ((T.filter (j ≤ ·)).min'_mem hne2)
      have hmin : ∀ k ∈ T, j ≤ k → k0 ≤ k := fun k hk hjk => (T.filter (j ≤ ·)).min'_le k (Finset.mem_filter.2 ⟨hk, hjk⟩)
      have hz : z ∈ colSpan F X {i | i ≤ k0} :=
        (keep_inv (hm k0 hk0.1) _).1 (Submodule.subset_span ⟨j, hk0.2, rfl⟩)
      have hle : colSpan F X {i | i ≤ k0} ≤
          (colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j}).comap ((matHom _ σ J u).1 - 1).mulVecLin := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨i, hi, rfl⟩
        have h1 := (hu1 i).2 _ (Submodule.subset_span ⟨i, Set.mem_singleton i, rfl⟩)
        have hsub : {l | ∃ k ∈ T, l ≤ k ∧ k < i} ⊆ {l | ∃ k ∈ T, l ≤ k ∧ k < j} := by
          rintro l ⟨k', hk', hlk', hk'i⟩
          refine ⟨k', hk', hlk', not_le.1 fun hjk' => ?_⟩
          exact absurd (hmin k' hk' hjk') (not_le.2 (lt_of_lt_of_le hk'i hi))
        have h2 := Submodule.span_mono (R := AF F ⊗[F] E) (Set.image_mono (f := fun i => (adMat F X)ᵀ i) hsub) h1
        change _ ∈ colSpan F X _ at h2
        simpa [sub_mulVec] using h2
      simpa [sub_mulVec] using hle hz
    · push_neg at hex
      have eAj : {i | ∃ k ∈ T, i ≤ k ∧ k < j} = {i | i ≤ T.max' hne} := by
        rw [← eB]
        exact Set.ext fun i => ⟨fun ⟨k, hk, h1, _⟩ => ⟨k, hk, h1⟩, fun ⟨k, hk, h1⟩ => ⟨k, hk, h1, hex k hk⟩⟩
      rw [eAj]
      have hxj : (adMat F X)ᵀ j ∈ colPerp σ J X {i | i ≤ T.max' hne} := by
        refine mem_colPerp_iff.2 (funext fun i => ?_)
        exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ (Xᵀ j) i).symm.trans
          ((congrArg _ (congrFun (congrFun hW.xx (i.castLE (T.max' hne).2)) j)).trans (map_zero _))
      exact hu2.2 z (perp_inv (hm _ hkMT) hxj)
  · rw [eB]
    refine ⟨keep_conj keepB hu2.1, fun y hy => ?_⟩
    rw [conj_sub]
    exact (keepB _).1 (hu2.2 _ (perp_inv (hm _ hkMT) hy))
