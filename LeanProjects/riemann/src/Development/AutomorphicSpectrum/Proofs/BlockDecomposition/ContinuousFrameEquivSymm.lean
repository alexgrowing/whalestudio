import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelFrame

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis

section Conj

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem conj_isom_iff (c : R →+* R) (B g : GL ι R) (D J : Matrix ι ι R)
    (h : (B : Matrix ι ι R)ᵀ * D * (B : Matrix ι ι R).map c = J) :
    (((B⁻¹ * g * B : GL ι R) : Matrix ι ι R)ᵀ * J * ((B⁻¹ * g * B : GL ι R) : Matrix ι ι R).map c = J) ↔
      (g : Matrix ι ι R)ᵀ * D * (g : Matrix ι ι R).map c = D := by
  have h1 : (((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * (B : Matrix ι ι R)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
  have h2 : (B : Matrix ι ι R).map c * ((B⁻¹ : GL ι R) : Matrix ι ι R).map c = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero c) (map_one c)]
  have h1' : (B : Matrix ι ι R)ᵀ * (((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
  have h2' : ((B⁻¹ : GL ι R) : Matrix ι ι R).map c * (B : Matrix ι ι R).map c = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero c) (map_one c)]
  have key : ((B⁻¹ * g * B : GL ι R) : Matrix ι ι R)ᵀ * J * ((B⁻¹ * g * B : GL ι R) : Matrix ι ι R).map c =
      (B : Matrix ι ι R)ᵀ * ((g : Matrix ι ι R)ᵀ * D * (g : Matrix ι ι R).map c) * (B : Matrix ι ι R).map c := by
    subst h
    simp only [Units.val_mul, Matrix.transpose_mul, Matrix.map_mul]
    calc _ = (B : Matrix ι ι R)ᵀ * (g : Matrix ι ι R)ᵀ * ((((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * (B : Matrix ι ι R)ᵀ) * D *
          ((B : Matrix ι ι R).map c * ((B⁻¹ : GL ι R) : Matrix ι ι R).map c) * (g : Matrix ι ι R).map c *
          (B : Matrix ι ι R).map c := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h2]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  rw [key]
  constructor
  · intro e
    have e' := congrArg (fun M => (((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * M * ((B⁻¹ : GL ι R) : Matrix ι ι R).map c) e
    subst h
    have l : ∀ M : Matrix ι ι R, (((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * ((B : Matrix ι ι R)ᵀ * M * (B : Matrix ι ι R).map c) *
        ((B⁻¹ : GL ι R) : Matrix ι ι R).map c = M := fun M => by
      calc _ = ((((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * (B : Matrix ι ι R)ᵀ) * M *
            ((B : Matrix ι ι R).map c * ((B⁻¹ : GL ι R) : Matrix ι ι R).map c) := by simp only [Matrix.mul_assoc]
        _ = M := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    rw [l] at e'
    rw [e', l]
  · intro e
    rw [e, h]

end Conj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

def bA (b : GL (Fin n ⊕ Fin n) E) : GL (Fin n ⊕ Fin n) (AE F E) :=
  Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) (inclR (F := F) (E := E) (AF F)) b

theorem bA_val (b : GL (Fin n ⊕ Fin n) E) :
    ((bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = incM F b.1 := rfl

theorem cA_inclR (σ : E →ₐ[F] E) (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [cA, inclR]

theorem gram_frame (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    ((bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))ᵀ *
        dbl (incM F Y.J) * ((bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).map
          (adCM σ χ).σ = Ad.J (AE F E) ε (Fin n) := by
  have := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E => M.map (inclR (F := F) (E := E) (AF F))) hb
  have e1 : (bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)).1.map (adCM σ χ).σ = (b.1.map σ).map (inclR (F := F) (E := E) (AF F)) := by
    ext i j
    exact cA_inclR σ _
  have e2 : dbl (incM F Y.J) = (dbl Y.J).map (inclR (F := F) (E := E) (AF F)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [dbl, incM]
  have e3 : (bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)).1ᵀ = (b.1ᵀ).map (inclR (F := F) (E := E) (AF F)) := rfl
  have e4 : Ad.J (AE F E) ε (Fin n) = (Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E).map (inclR (F := F) (E := E) (AF F)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> by_cases h : i = j <;> simp [Ad.J, h, Matrix.one_apply]
  rw [e1, e2, e3, e4, ← this]
  simp only [Matrix.map_mul]

def frameEquiv (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    G2 σ Y ≃* (adCM σ χ).U ε (Fin n) where
  toFun x := ⟨(bA b)⁻¹ * x.1 * bA b, (conj_isom_iff (adCM σ χ).σ (bA b) x.1 _ _ (gram_frame χ ε b hb)).2 x.2⟩
  invFun y := ⟨bA b * y.1 * (bA b)⁻¹, by
    have h := (conj_isom_iff (adCM σ χ).σ (bA (F := F) b) (bA b * y.1 * (bA b)⁻¹) _ _ (gram_frame χ ε b hb)).1
    apply h
    have : (bA (F := F) b)⁻¹ * (bA b * y.1 * (bA b)⁻¹) * bA b = y.1 := by group
    rw [this]
    exact y.2⟩
  left_inv x := by
    apply Subtype.ext
    show bA b * ((bA b)⁻¹ * x.1 * bA b) * (bA b)⁻¹ = x.1
    group
  right_inv y := by
    apply Subtype.ext
    show (bA b)⁻¹ * (bA b * y.1 * (bA b)⁻¹) * bA b = y.1
    group
  map_mul' x y := by
    apply Subtype.ext
    show (bA b)⁻¹ * (x.1 * y.1) * bA b = ((bA b)⁻¹ * x.1 * bA b) * ((bA b)⁻¹ * y.1 * bA b)
    group

theorem frameEquiv_val (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (x : G2 σ Y) :
    (frameEquiv χ ε b hb x).1 = (bA b)⁻¹ * x.1 * bA b := rfl

theorem frameEquiv_symm_val (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (y : (adCM σ χ).U ε (Fin n)) :
    ((frameEquiv χ ε b hb).symm y).1 = bA b * y.1 * (bA b)⁻¹ := rfl

theorem continuous_frameEquiv (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    Continuous (frameEquiv χ ε b hb) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem continuous_frameEquiv_symm (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    Continuous (frameEquiv χ ε b hb).symm := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

end GlobalTheory.CompanionTheory.SiegelFrame
