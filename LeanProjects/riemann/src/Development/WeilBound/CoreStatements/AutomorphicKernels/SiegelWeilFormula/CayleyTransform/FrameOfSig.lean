import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RdExOf

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Krd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField F] [NumberField E] in

theorem conjT_frame {n : ℕ} (c : E) (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = c * J i j)
    (hss : ∀ x, σ (σ x) = x) (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) :
    ((b.transpose * dbl J * b.map σ).map σ).transpose = c • (b.transpose * dbl J * b.map σ) := by
  have hm : ∀ {p q r : Type} [Fintype q] (X : Matrix p q E) (Z : Matrix q r E), (X * Z).map σ = X.map σ * Z.map σ :=
    fun X Z => Matrix.map_mul (f := σ.toRingHom)
  have h1 : ((dbl J).map σ).transpose = c • dbl J := by
    ext (p | p) (q | q) <;> simp [dbl, Matrix.fromBlocks, hJ]
  have hb : (b.map σ).map σ = b := by ext; simp [hss]
  rw [hm, hm, Matrix.transpose_mul, Matrix.transpose_mul, hb, h1, ← Matrix.transpose_map, Matrix.transpose_transpose,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

theorem epsEx : EpsEx := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  refine ⟨ε, hε, ?_⟩
  have hss : ∀ x, σ (σ x) = x := PositivityTheory.ThKG.Tow.Levi.sig_sig d.cm
  have i : Fin d.n := ⟨0, d.ok.hn⟩
  have key : ∀ c : E, (∀ i j, σ (d.Y.J j i) = c * d.Y.J i j) → ((ε : ℤ) : E) = c := fun c hc => by
    have e := congrFun (congrFun (conjT_frame c d.Y.J hc hss d.b.1) (Sum.inl i)) (Sum.inr i)
    rw [hε] at e
    simpa [Matrix.fromBlocks] using e
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · refine Or.inl ⟨hA, ?_⟩
    have e := key (-1) fun i j => by rw [hY, neg_one_mul]
    have e' : ((ε : ℤ) : E) = ((-1 : ℤ) : E) := by rw [e]; push_cast; rfl
    exact Units.ext (by simpa using Int.cast_injective (α := E) e')
  · refine Or.inr ⟨hA, ?_⟩
    have e := key 1 fun i j => by rw [hY, one_mul]
    have e' : ((ε : ℤ) : E) = ((1 : ℤ) : E) := by rw [e]; push_cast; rfl
    exact Units.ext (by simpa using Int.cast_injective (α := E) e')

theorem frame_of_sig {m r s : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : HasSig M r s) (h0 : min r s = 0) :
    ∃ (f : GL (Fin m) ℂ) (sg : ℤˣ), f.1.transpose * M * f.1.map star = ((sg : ℤ) : ℂ) • 1 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin m ≃ Fin r ⊕ Fin s := (finSumFinEquiv.trans (finCongr hrs)).symm
  let f0 : Matrix (Fin m) (Fin m) ℂ := A.submatrix id e
  have hf0 : f0.transpose * M * f0.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e e := by
    rw [← hA]
    ext i j
    simp only [f0, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply, id]
  have main : ∃ sg : ℤˣ, f0.transpose * M * f0.map star = ((sg : ℤ) : ℂ) • 1 := by
    rcases Nat.min_eq_zero_iff.1 h0 with rfl | rfl
    · refine ⟨-1, ?_⟩
      rw [hf0, show (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin 0 ⊕ Fin s) (Fin 0 ⊕ Fin s) ℂ) = -1 by
        ext (i | i) (j | j) <;> first | exact i.elim0 | exact j.elim0 | simp [Matrix.one_apply]]
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.neg_apply, Matrix.one_apply, e.injective.eq_iff, Matrix.smul_apply]
      split_ifs <;> simp
    · refine ⟨1, ?_⟩
      rw [hf0, show (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ) = 1 by
        ext (i | i) (j | j) <;> first | exact i.elim0 | exact j.elim0 | simp [Matrix.one_apply]]
      ext i j
      simp [Matrix.one_apply, e.injective.eq_iff]
  obtain ⟨sg, hsg⟩ := main
  have hdet : f0.det ≠ 0 := by
    intro h0'
    have e1 := congrArg Matrix.det hsg
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0', zero_mul, zero_mul, Matrix.det_smul,
      Matrix.det_one, mul_one] at e1
    exact pow_ne_zero _ (Int.cast_ne_zero.2 (Units.ne_zero sg)) e1.symm
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero f0 hdet, sg, hsg⟩

theorem frEx : FrEx := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun hA => ?_, fun hA => ?_⟩
  · choose fr sg hfr using fun w => frame_of_sig (hA.sig w) d.ok.aniso
    exact ⟨fr, sg, fun w => by rw [one_smul, hfr w]⟩
  · choose fr sg hfr using fun w => frame_of_sig (hA.sig w) d.ok.aniso
    refine ⟨fr, sg, fun w => ?_⟩
    rw [← hfr w, Matrix.mul_smul, Matrix.smul_mul]

end PositivityTheory.SiegelWeilFormula.Krd

end
