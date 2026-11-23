import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelFrame.ParStab

section Linear

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

def firstCols (R : Type) [CommRing R] (ι : Type) [DecidableEq ι] : Matrix (ι ⊕ ι) ι R := Matrix.fromRows 1 0

theorem mul_firstCols (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) : g * firstCols R ι = g.toCols₁ := by
  ext r j
  simp [firstCols, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]

theorem firstCols_mul_apply_inl (m : Matrix ι ι R) (i j : ι) : (firstCols R ι * m) (Sum.inl i) j = m i j := by
  simp [firstCols, Matrix.mul_apply, Matrix.one_apply]

theorem firstCols_mul_apply_inr (m : Matrix ι ι R) (i j : ι) : (firstCols R ι * m) (Sum.inr i) j = 0 := by
  simp [firstCols, Matrix.mul_apply]

theorem firstCols_cancel {m m' : Matrix ι ι R} (h : firstCols R ι * m = firstCols R ι * m') : m = m' := by
  ext i j
  rw [← firstCols_mul_apply_inl m, h, firstCols_mul_apply_inl]

theorem low_zero_of_mul {g : Matrix (ι ⊕ ι) (ι ⊕ ι) R} {m : Matrix ι ι R} (h : g * firstCols R ι = firstCols R ι * m)
    (i j : ι) : g (Sum.inr i) (Sum.inl j) = 0 := by
  have := congrFun (congrFun h (Sum.inr i)) j
  rwa [mul_firstCols, firstCols_mul_apply_inr] at this

theorem mul_eq_of_low_zero {g : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (h : ∀ i j, g (Sum.inr i) (Sum.inl j) = 0) :
    g * firstCols R ι = firstCols R ι * g.toBlocks₁₁ := by
  ext r j
  rcases r with i | i
  · rw [firstCols_mul_apply_inl, mul_firstCols]; rfl
  · rw [firstCols_mul_apply_inr, mul_firstCols]; exact h i j

theorem mem_stab_iff (g : GL (ι ⊕ ι) R) : g ∈ stab R (Sum.inl '' (Set.univ : Set ι)) ↔
    ∀ i j, (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr i) (Sum.inl j) = 0 ∧
      ((g⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr i) (Sum.inl j) = 0 := by
  constructor
  · intro h i j
    exact h (Sum.inr i) (by simp) (Sum.inl j) (by simp)
  · intro h r hr c hc
    obtain ⟨j, -, rfl⟩ := hc
    rcases r with i | i
    · exact absurd ⟨i, Set.mem_univ _, rfl⟩ hr
    · exact h i j

theorem exists_mul_eq_iff_mem_stab (B x : GL (ι ⊕ ι) R) (D : Matrix (ι ⊕ ι) ι R) (T : GL ι R)
    (hB : (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι = D * (T : Matrix ι ι R)) :
    (∃ t : GL ι R, (x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D = D * (t : Matrix ι ι R)) ↔
      B⁻¹ * x * B ∈ stab R (Sum.inl '' (Set.univ : Set ι)) := by
  have hBi : ((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hTi : (T : Matrix ι ι R) * ((T⁻¹ : GL ι R) : Matrix ι ι R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hD : D = (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι * ((T⁻¹ : GL ι R) : Matrix ι ι R) := by
    rw [hB, Matrix.mul_assoc, hTi, Matrix.mul_one]
  have hC : ((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D * (T : Matrix ι ι R) = firstCols R ι := by
    rw [Matrix.mul_assoc, ← hB, ← Matrix.mul_assoc, hBi, Matrix.one_mul]
  have hinv : (B⁻¹ * x * B)⁻¹ = B⁻¹ * x⁻¹ * B := by group
  have key : ∀ (g : GL (ι ⊕ ι) R) (s : Matrix ι ι R), (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D = D * s →
      ((B⁻¹ * g * B : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι =
        firstCols R ι * (((T⁻¹ : GL ι R) : Matrix ι ι R) * s * (T : Matrix ι ι R)) := by
    intro g s hg
    calc _ = ((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * ((g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D) * (T : Matrix ι ι R) := by
          simp only [Units.val_mul, Matrix.mul_assoc]
          rw [hB]
      _ = ((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D * (s * (T : Matrix ι ι R)) := by
          rw [hg]; simp only [Matrix.mul_assoc]
      _ = (((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D * (T : Matrix ι ι R)) *
            (((T⁻¹ : GL ι R) : Matrix ι ι R) * s * (T : Matrix ι ι R)) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (T : Matrix ι ι R) (((T⁻¹ : GL ι R) : Matrix ι ι R)), hTi, Matrix.one_mul]
      _ = _ := by rw [hC]
  constructor
  · rintro ⟨t, ht⟩
    have hx' : ((x⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D = D * ((t⁻¹ : GL ι R) : Matrix ι ι R) := by
      have h1 : ((x⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have h2 : (t : Matrix ι ι R) * ((t⁻¹ : GL ι R) : Matrix ι ι R) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc _ = ((x⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (D * ((t : Matrix ι ι R) * ((t⁻¹ : GL ι R) : Matrix ι ι R))) := by
            rw [h2, Matrix.mul_one]
        _ = ((x⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * ((x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D) * ((t⁻¹ : GL ι R) : Matrix ι ι R) := by
            rw [ht]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [mem_stab_iff]
    intro i j
    refine ⟨low_zero_of_mul (key x _ ht) i j, ?_⟩
    rw [hinv]
    exact low_zero_of_mul (key x⁻¹ _ hx') i j
  · intro hy
    rw [mem_stab_iff] at hy
    set y : GL (ι ⊕ ι) R := B⁻¹ * x * B with hydef
    have e1 := mul_eq_of_low_zero fun i j => (hy i j).1
    have e2 := mul_eq_of_low_zero fun i j => (hy i j).2
    set m := (y : Matrix (ι ⊕ ι) (ι ⊕ ι) R).toBlocks₁₁ with hm
    set m' := ((y⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).toBlocks₁₁ with hm'
    have hyy : (y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * ((y⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hyy' : ((y⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hmm : m * m' = 1 := by
      apply firstCols_cancel
      rw [← Matrix.mul_assoc, ← e1, Matrix.mul_assoc, ← e2, ← Matrix.mul_assoc, hyy, Matrix.one_mul, Matrix.mul_one]
    have hmm' : m' * m = 1 := by
      apply firstCols_cancel
      rw [← Matrix.mul_assoc, ← e2, Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, hyy', Matrix.one_mul, Matrix.mul_one]
    let u : GL ι R := ⟨m, m', hmm, hmm'⟩
    refine ⟨T * u * T⁻¹, ?_⟩
    have hx : (x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
        (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      rw [hydef]
      group
    calc _ = (x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι * ((T⁻¹ : GL ι R) : Matrix ι ι R) := by
          conv_lhs => rw [hD]
          simp only [Matrix.mul_assoc]
      _ = (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * ((y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι) * ((T⁻¹ : GL ι R) : Matrix ι ι R) := by
          rw [hx]; simp only [Matrix.mul_assoc]
      _ = (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι * (m * ((T⁻¹ : GL ι R) : Matrix ι ι R)) := by
          rw [e1]; simp only [Matrix.mul_assoc]
      _ = D * (T : Matrix ι ι R) * (m * ((T⁻¹ : GL ι R) : Matrix ι ι R)) := by rw [hB]
      _ = _ := by
          simp only [Units.val_mul, Matrix.mul_assoc]
          rfl

end Linear

theorem exists_isPar_iff_mem_uQ : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (t₀ : GL (Fin n) E), b.1.toCols₁ = diagCols (Fin n) * t₀.1 → ∀ x : G2 σ Y, (∃ t, IsPar x t) ↔ frameEquiv χ ε b hb x ∈ (adCM σ χ).uQ ε (Set.univ : Set (Fin n)) := by
  intro F E _ _ _ _ _ σ n Y χ ε b hb t₀ ht x
  have hdiag : (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E).map (inclR (F := F) (E := E) (AF F)) =
      diagCols (Fin n) := by
    ext r j
    rcases r with i | i <;> by_cases h : i = j <;> simp [diagCols, Matrix.one_apply, h]
  have hB : ((bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * firstCols (AE F E) (Fin n) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * ((Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)) t₀ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [mul_firstCols, ← hdiag]
    have ht' : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * (t₀.1 : Matrix (Fin n) (Fin n) E) := ht
    have := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n) E => M.map (inclR (F := F) (E := E) (AF F))) ht'
    simp only [Matrix.map_mul] at this
    exact this
  have h := exists_mul_eq_iff_mem_stab (bA (F := F) b) x.1 (diagCols (Fin n)) _ hB
  rw [PositivityTheory.RgEis.Ad.uQ, Subgroup.mem_subgroupOf, frameEquiv_val]
  exact h

end GlobalTheory.CompanionTheory.SiegelFrame.ParStab
