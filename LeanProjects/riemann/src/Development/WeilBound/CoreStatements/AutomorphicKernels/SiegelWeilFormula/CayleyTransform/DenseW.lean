import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.UnitaryGroupInverseFormula

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Krd.DM

open PositivityTheory.SiegelWeilFormula.Krd.DC

theorem conj_unitE {K ι : Type} [CommRing K] [Fintype ι] [DecidableEq ι] (f : K →+* K) (b bi Z D Q : Matrix ι ι K)
    (hb : b * bi = 1) (hQ : bᵀ * D * b.map f = Q) (hZ : Zᵀ * Q * Z.map f = Q) :
    (b * Z * bi)ᵀ * D * (b * Z * bi).map f = D := by
  have h1 : (1 : Matrix ι ι K).map f = 1 := Matrix.map_one _ (map_zero f) (map_one f)
  have hD : D = biᵀ * Q * bi.map f := by
    calc D = (b * bi)ᵀ * D * (b * bi).map f := by
          rw [hb, Matrix.transpose_one, h1, Matrix.one_mul, Matrix.mul_one]
      _ = biᵀ * (bᵀ * D * b.map f) * bi.map f := by
          rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = biᵀ * Q * bi.map f := by rw [hQ]
  calc (b * Z * bi)ᵀ * D * (b * Z * bi).map f = biᵀ * (Zᵀ * (bᵀ * D * b.map f) * Z.map f) * bi.map f := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.map_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
    _ = D := by rw [hQ, hZ, ← hD]

theorem det_ne_of {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (f : K →+* K) {A D : Matrix ι ι K}
    (h : Aᵀ * D * A.map f = D) (hD : D.det ≠ 0) : A.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul] at this
  exact hD this.symm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_cA {p q : Type} (M : Matrix p q E) : (incM F M).map (cA σ) = incM F (M.map σ) := by
  ext i j
  rfl

theorem incM_alt_bis {p q : Type} (M : Matrix p q E) : (incM F M)ᵀ = incM F Mᵀ :=
  Matrix.transpose_map.symm

variable (d : SD σ)

theorem dblJ_det {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε) : (dbl d.Y.J).det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det hε
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul] at this
  exact QR_det_ne E ε this.symm

def bX (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E :=
  d.b.1 * X * (d.b⁻¹).1

theorem bX_unitary {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    {X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E} (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    (bX d X)ᵀ * dbl d.Y.J * (bX d X).map σ = dbl d.Y.J :=
  conj_unitE (σ : E →+* E) d.b.1 (d.b⁻¹).1 X (dbl d.Y.J) (QR E d.n ε) (Units.mul_inv d.b) hε hX

def ratG {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) : d.G :=
  ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F))
    (Matrix.nonsingInvUnit (bX d X) (isUnit_iff_ne_zero.2 (det_ne_of (σ : E →+* E) (bX_unitary d hε hX) (dblJ_det d hε)))),
    by
      show (incM F (bX d X))ᵀ * dbl (incM F d.Y.J) * (incM F (bX d X)).map (cA σ) = dbl (incM F d.Y.J)
      rw [dbl_incM d, incM_cA, incM_alt_bis, ← incM_mul, ← incM_mul, bX_unitary d hε hX]⟩

theorem ratG_mem {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    ratG d hε X hX ∈ rat2 σ d.Y :=
  Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩

theorem inFrame_ratG {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    inFrame d.b (ratG d hε X hX) = incM F X := by
  show incM F (d.b⁻¹).1 * incM F (bX d X) * incM F d.b.1 = incM F X
  rw [← incM_mul, ← incM_mul]
  congr 1
  simp only [bX, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem inFrame_mul (x z : d.G) : inFrame d.b (x * z) = inFrame d.b x * inFrame d.b z := by
  show incM F (d.b⁻¹).1 * (mat2 x * mat2 z) * incM F d.b.1 =
    (incM F (d.b⁻¹).1 * mat2 x * incM F d.b.1) * (incM F (d.b⁻¹).1 * mat2 z * incM F d.b.1)
  calc incM F (d.b⁻¹).1 * (mat2 x * mat2 z) * incM F d.b.1 =
      incM F (d.b⁻¹).1 * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 z * incM F d.b.1 := by
        rw [bb d, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem inFrame_inj {x z : d.G} (h : inFrame d.b x = inFrame d.b z) : x = z := by
  have e : ∀ u : d.G, mat2 u = incM F d.b.1 * inFrame d.b u * incM F (d.b⁻¹).1 := fun u => by
    simp only [inFrame, ← Matrix.mul_assoc, bb d, Matrix.one_mul]
    rw [Matrix.mul_assoc, bb d, Matrix.mul_one]
  apply Subtype.ext
  apply Units.ext
  show mat2 x = mat2 z
  rw [e x, e z, h]

theorem J_unit (ε : ℤˣ) {n : ℕ} : IsUnit (Qc n ε)ᵀ.det := by
  refine Matrix.isUnit_det_of_right_inverse (B := ((ε : ℤ) : ℂ)⁻¹ • (Qc n ε)ᵀ) ?_
  rw [Matrix.mul_smul, J_sq, smul_smul, inv_mul_cancel₀ (eps_ne ε), one_smul]

theorem det_of_inU {ε : ℤˣ} {n : ℕ} {h : M2 n} (hh : InU (Qc n ε)ᵀ h) : IsUnit h.det := by
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  have := congrArg Matrix.det hh
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
  exact (J_unit ε).ne_zero this.symm

end PositivityTheory.SiegelWeilFormula.Krd.DM

open PositivityTheory.SiegelWeilFormula.Krd PositivityTheory.SiegelWeilFormula.Krd.DM PositivityTheory.SiegelWeilFormula.Krd.DC in

theorem PositivityTheory.SiegelWeilFormula.Krd.denseW : PositivityTheory.SiegelWeilFormula.DenseW := by
  intro F E _ _ _ _ _ σ d R w y O hO hy
  have h0 := zeta_ne R.hζ
  have hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n R.ε := R.hε
  obtain ⟨X, hXU, hXO⟩ := exists_rat d.cm (d.B.emb w).1 R.hζ hO hy
  have hX := rat_unitary d.cm (d.B.emb w).1 R.ε X hXU
  refine ⟨ratG d hε X hX, ratG_mem d hε X hX, _, hXO, ratG d hε X hX * (R.ι w (Phi R.hζ ⟨_, hXU⟩))⁻¹,
    (inv_mul_cancel_right _ _).symm, fun y'' => ?_⟩
  set y' := Phi R.hζ ⟨X.map (d.B.emb w).1, hXU⟩ with hy'
  set A := inFrame d.b (ratG d hε X hX * (R.ι w y')⁻¹) with hA
  have hAC : A * inFrame d.b (R.ι w y') = incM F X := by
    rw [hA, ← inFrame_mul, inv_mul_cancel_right, inFrame_ratG]
  have hC : d.cw w (inFrame d.b (R.ι w y')) = X.map (d.B.emb w).1 := by
    have e := R.at_w w y'
    rw [show mR y' = dZ d.n R.ζ * X.map (d.B.emb w).1 * dZ d.n R.ζ⁻¹ from rfl, Matrix.mul_assoc _ (dZ _ R.ζ⁻¹),
      dZ_inv_mul h0, Matrix.mul_one] at e
    have := congrArg (fun M => dZ d.n R.ζ⁻¹ * M) e
    simpa only [← Matrix.mul_assoc, dZ_inv_mul h0, Matrix.one_mul] using this
  have hdet := det_of_inU hXU
  have hAw : d.cw w A = 1 := by
    have e : d.cw w A * X.map (d.B.emb w).1 = X.map (d.B.emb w).1 := by
      have := congrArg (d.cw w) hAC
      rwa [cw_mul, hC, cw_incM] at this
    calc d.cw w A = d.cw w A * X.map (d.B.emb w).1 * (X.map (d.B.emb w).1)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = 1 := by rw [e, Matrix.mul_nonsing_inv _ hdet]
  apply inFrame_inj d
  rw [inFrame_mul d _ (R.ι w y''), inFrame_mul d (R.ι w y''), ← hA]
  refine Place.cw_ext d (fun w' => ?_) ?_
  · rw [cw_mul, cw_mul]
    by_cases hw : w' = w
    · subst hw; rw [hAw, Matrix.one_mul, Matrix.mul_one]
    · rw [R.off_w w w' y'' hw, Matrix.one_mul, Matrix.mul_one]
  · rw [fin_mul, fin_mul, R.off_f w y'', ← fin_mul, ← fin_mul, Matrix.mul_one, Matrix.one_mul]

end
