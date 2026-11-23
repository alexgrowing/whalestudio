import Mathlib

theorem UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.aux1 :
    ∀ (Ω : Type) [inst : Field Ω] [inst_1 : CharZero Ω], Module.IsTorsionFree ℚ Ω := by
  intro Ω _ _
  infer_instance

theorem UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.aux2 :
    ∀ (L Ω : Type) [inst : Field L] [inst_1 : Field Ω] [inst_2 : Algebra L Ω], Module.IsTorsionFree L Ω := by
  intro L Ω _ _ _
  infer_instance

@[reducible] noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Dec.{u_1, u_2} :
    {F : Type u_1} →
      {Ω : Type u_2} →
        [inst : Field F] →
          [inst_1 : Field Ω] → [inst_2 : Algebra F Ω] → ValuationSubring Ω → Subgroup (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω) :=
    fun {F : Type u_1} {Ω : Type u_2} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) ↦
      ValuationSubring.decompositionSubgroup F A

theorem UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.aux6.{u_1} :
    ∀ (Ω : Type u_1) [inst : Field Ω], IsDomain Ω := by
  intro Ω _
  infer_instance

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.FreeRatios :
    {κ ι : Type} → [inst : Field κ] → (ι → κˣ) → Prop :=
    fun {κ ι : Type} [Field κ] (α : ι → κˣ) ↦ ∀ (i j : ι), i ≠ j → ∀ (m : ℕ), (0 : ℕ) < m → α i ^ m ≠ α j ^ m

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.mat :
    {H k : Type} → [inst : Group H] → [inst_1 : CommRing k] → {n : ℕ} → (H →* GL (Fin n) k) → H →* Matrix (Fin n) (Fin n) k :=
    fun {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k) ↦
      (Units.coeHom (Matrix (Fin n) (Fin n) k)).comp r

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.FreeAt :
    (l : ℕ) →
      [inst : Fact (Nat.Prime l)] →
        {F Ω : Type} →
          [inst_1 : Field F] →
            [inst_2 : Field Ω] →
              [inst_3 : Algebra F Ω] → {n : ℕ} → (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω →* GL (Fin n) (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l)) → Prop :=
    fun (l : ℕ) [Fact (Nat.Prime l)] {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {n : ℕ}
        (r : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω →* GL (Fin n) (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l)) ↦
      ∀ (A : ValuationSubring Ω),
        (A.valuation : Ω → A.ValueGroup) (↑l : Ω) < (1 : A.ValueGroup) →
          ∃ g ∈ UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Dec A,
            (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.cycZ F Ω l : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω → ℤ_[l]ˣ) g = (1 : ℤ_[l]ˣ) ∧
              ∃ (α : Fin n → (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l)ˣ),
                UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.FreeRatios α ∧
                  ((UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.mat r : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω → Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l))
                        g).charpoly =
                    ∏ i : Fin n,
                      (Polynomial.X -
                        (Polynomial.C : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l → Polynomial (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l))
                          (↑(α i) : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l))

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.galEmb :
    (k E Ω : Type) →
      [inst : Field k] →
        [inst_1 : Field E] →
          [inst_2 : Field Ω] →
            [inst_3 : Algebra k Ω] →
              [inst_4 : Algebra E Ω] →
                [inst_5 : Algebra k E] → [IsScalarTower k E Ω] → UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G E Ω →* UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G k Ω :=
    fun (k E Ω : Type) [Field k] [Field E] [Field Ω] [Algebra k Ω] [Algebra E Ω] [Algebra k E] [IsScalarTower k E Ω] ↦
      AlgEquiv.restrictScalarsHom k

private theorem UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.charpoly_pow_two {k : Type} [Field k] (M : Matrix (Fin 2) (Fin 2) k) (a b : k)
    (h : M.charpoly = (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b)) (m : ℕ) :
    (M ^ m).charpoly = (Polynomial.X - Polynomial.C (a ^ m)) * (Polynomial.X - Polynomial.C (b ^ m)) := by
  have ht : M.trace = a + b := by
    have h0 := congrArg (fun p => Polynomial.eval 0 p) h
    have h1 := congrArg (fun p => Polynomial.eval 1 p) h
    rw [Matrix.charpoly_fin_two] at h0 h1
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at h0 h1
    linear_combination h0 - h1
  have hd : M.det = a * b := by
    have h1 := congrArg (fun p => Polynomial.eval 0 p) h
    rw [Matrix.charpoly_fin_two] at h1
    simpa using h1
  have hsq : M ^ 2 = (a + b) • M - (a * b) • (1 : Matrix (Fin 2) (Fin 2) k) := by
    rw [← ht, ← hd, Matrix.trace_fin_two, Matrix.det_fin_two, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have htr : ∀ n : ℕ, (M ^ n).trace = a ^ n + b ^ n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simp [one_add_one_eq_two]
    | one => simpa using ht
    | more n h0 h1 =>
      rw [pow_add M n 2, hsq, mul_sub, Matrix.mul_smul, Matrix.mul_smul, mul_one, ← pow_succ,
        Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, h0, h1, smul_eq_mul, smul_eq_mul]
      ring
  rw [Matrix.charpoly_fin_two, htr, Matrix.det_pow, hd, mul_pow, Polynomial.C_add, Polynomial.C_mul]
  ring

private theorem UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.exists_pow_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (L : Type)
    [Field L] [NumberField L] [Algebra L Ω] (g : Gal(Ω/ℚ)) :
    ∃ m : ℕ, 0 < m ∧ ∃ g' : Gal(Ω/L), AlgEquiv.restrictScalarsHom ℚ g' = g ^ m := by
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ L Ω).fieldRange
  haveI : FiniteDimensional ℚ K :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ L Ω)).toLinearEquiv.finiteDimensional
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hi : K.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨m, hm, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hi g
  rw [IntermediateField.mem_fixingSubgroup_iff] at hmem
  refine ⟨m, hm, AlgEquiv.ofRingEquiv (f := (g ^ m).toRingEquiv) (fun x => hmem _ ⟨x, rfl⟩), ?_⟩
  ext x
  rfl

theorem UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.freeRes :
    ∀ {Ω : Type} [inst : Field Ω] [inst_1 : CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [inst_3 : Fact (Nat.Prime l)] (L : Type)
      [inst_4 : Field L] [inst_5 : NumberField L] [inst_6 : Algebra L Ω] [IsAlgClosure L Ω]
      (W : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G ℚ Ω →* GL (Fin (2 : ℕ)) (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l)),
      UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.FreeAt l W → UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.FreeAt l (W.comp (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.galEmb ℚ L Ω)) := by
  intro Ω _ _ _ l _ L _ _ _ _ W hW A hA
  obtain ⟨g, hgD, hgc, α, hα, hch⟩ := hW A hA
  obtain ⟨m, hm, g', hg'⟩ := UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.exists_pow_fix L g
  refine ⟨g', ?_, ?_, fun i => α i ^ m, ?_, ?_⟩
  · have h1 : g ^ m ∈ UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Dec A := Subgroup.pow_mem _ hgD m
    rw [← hg'] at h1
    exact h1
  · have h1 : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.cycZ ℚ Ω l (g ^ m) = 1 := by rw [map_pow, hgc, one_pow]
    rw [← hg'] at h1
    exact h1
  · intro i j hij n hn
    have h1 := hα i j hij (m * n) (Nat.mul_pos hm hn)
    simpa only [pow_mul] using h1
  · have h1 : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.mat (W.comp (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.galEmb ℚ L Ω)) g' = UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.mat W g ^ m := by
      rw [← map_pow, ← hg']
      rfl
    rw [Fin.prod_univ_two] at hch
    rw [h1, Fin.prod_univ_two, UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.charpoly_pow_two _ _ _ hch m]
    simp only [Units.val_pow_eq_pow_val]
