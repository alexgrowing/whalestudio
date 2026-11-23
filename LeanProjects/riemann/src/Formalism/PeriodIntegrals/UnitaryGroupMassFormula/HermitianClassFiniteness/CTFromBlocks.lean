import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.HformSumRight

noncomputable section

open NumberField Matrix Formalism.UG PI.InHHClassFin
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.InHHClassFin

variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}

abbrev AA (I : Formalism.MainNotions.S.AutInst) : Type := I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F

abbrev ιA (I : Formalism.MainNotions.S.AutInst) : I.E →+* AA I := inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)

abbrev σA (I : Formalism.MainNotions.S.AutInst) : AA I →+* AA I := sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)

theorem σA_ιA (e : I.E) : σA I (ιA I e) = ιA I (starRingEnd I.E e) := by
  first
  | (show (Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Formalism.MainNotions.S.Af I.F))) (e ⊗ₜ[I.F] 1) =
        (starRingEnd I.E e) ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F)
     rw [Algebra.TensorProduct.map_tmul]
     rfl)
  | (simp [sigR, inclE]; rfl)

theorem cT_map {p q : Type} (M : Matrix p q I.E) :
    cT (σA I) (M.map (ιA I)) = (cT (starRingEnd I.E) M).map (ιA I) := by
  ext i j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  exact σA_ιA _

theorem cT_one' {p : Type} [DecidableEq p] {A : Type} [CommRing A] (σ : A →+* A) :
    cT σ (1 : Matrix p p A) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [cT]
  · simp [cT, Matrix.one_apply, hij, Ne.symm hij]

theorem cT_zero' {p q : Type} {A : Type} [CommRing A] (σ : A →+* A) :
    cT σ (0 : Matrix p q A) = 0 := by
  ext i j
  simp [cT]

theorem cT_mulG {A : Type} [CommRing A] (σ : A →+* A) {m p q : Type} [Fintype p]
    (M : Matrix m p A) (N : Matrix p q A) : cT σ (M * N) = cT σ N * cT σ M := by
  rw [cT, cT, cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_fromBlocks {A : Type} [CommRing A] (σ : A →+* A) {a b c d : Type}
    (P : Matrix a c A) (Q : Matrix a d A) (R : Matrix b c A) (T : Matrix b d A) :
    cT σ (Matrix.fromBlocks P Q R T) = Matrix.fromBlocks (cT σ P) (cT σ R) (cT σ Q) (cT σ T) := by
  simp only [cT, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

section Frame

variable (fr : Frame I S)

abbrev Frame.BA : Matrix (Fin I.n) (Fin fr.m ⊕ Fin fr.k) (AA I) := fr.B.map (ιA I)

abbrev Frame.BiA : Matrix (Fin fr.m ⊕ Fin fr.k) (Fin I.n) (AA I) := fr.Bi.map (ιA I)

theorem Frame.BA_BiA : fr.BA * fr.BiA = 1 := by
  show fr.B.map (ιA I) * fr.Bi.map (ιA I) = 1
  rw [← Matrix.map_mul, fr.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem Frame.BiA_BA : fr.BiA * fr.BA = 1 := by
  show fr.Bi.map (ιA I) * fr.B.map (ιA I) = 1
  rw [← Matrix.map_mul, fr.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

abbrev JA (I : Formalism.MainNotions.S.AutInst) : Matrix (Fin I.n) (Fin I.n) (AA I) := I.J.map (ιA I)

theorem Frame.JtA : fr.Jt.map (ιA I) = cT (σA I) fr.BA * JA I * fr.BA := by
  rw [Frame.Jt, Matrix.map_mul, Matrix.map_mul, ← cT_map]

theorem Frame.JtA_blocks : fr.Jt.map (ιA I) =
    Matrix.fromBlocks (fr.Jt.toBlocks₁₁.map (ιA I)) 0 0 (fr.J'.map (ιA I)) := by
  conv_lhs => rw [fr.Jt_blocks]
  simp [Matrix.fromBlocks_map]

theorem mem_UPts_iff {k : Type} [Fintype k] [DecidableEq k] (J : Matrix k k I.E)
    (x : GL k (AA I)) : x ∈ UPts I.cm.sig J (Formalism.MainNotions.S.Af I.F) ↔
      cT (σA I) (x : Matrix k k (AA I)) * J.map (ιA I) * (x : Matrix k k (AA I)) = J.map (ιA I) :=
  Iff.rfl

theorem unit_cancel {k : Type} [Fintype k] [DecidableEq k] (P : Matrix k k I.E) (hP : P.det ≠ 0)
    (X : Matrix k (Fin fr.k) (AA I)) (h : P.map (ιA I) * X = 0) : X = 0 := by
  have h1 : (P⁻¹).map (ιA I) * (P.map (ιA I) * X) = X := by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hP),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rw [h, Matrix.mul_zero] at h1
  exact h1.symm

theorem fix_span (h : HfinS I S) (u : Fin I.n → I.E) (hu : u ∈ Submodule.span I.E S) :
    I.fmat (h : I.Gf) *ᵥ (fun i => ιA I (u i)) = fun i => ιA I (u i) := by
  induction hu using Submodule.span_induction with
  | mem x hx => exact h.2 x hx
  | zero =>
    have e1 : (fun i => ιA I ((0 : Fin I.n → I.E) i)) = 0 := by
      ext i
      simp
    rw [e1, Matrix.mulVec_zero]
  | add x y _ _ hx hy =>
    have e1 : (fun i => ιA I ((x + y) i)) = (fun i => ιA I (x i)) + (fun i => ιA I (y i)) := by
      ext i
      simp
    rw [e1, Matrix.mulVec_add, hx, hy]
  | smul a x _ hx =>
    have e1 : (fun i => ιA I ((a • x) i)) = ιA I a • (fun i => ιA I (x i)) := by
      ext i
      simp
    rw [e1, Matrix.mulVec_smul, hx]

def Frame.MA (h : HfinS I S) : Matrix (Fin fr.m ⊕ Fin fr.k) (Fin fr.m ⊕ Fin fr.k) (AA I) :=
  fr.BiA * I.fmat (h : I.Gf) * fr.BA

theorem Frame.MA_inl (h : HfinS I S) (p : Fin fr.m ⊕ Fin fr.k) (j : Fin fr.m) :
    fr.MA h p (Sum.inl j) = (1 : Matrix (Fin fr.m ⊕ Fin fr.k) (Fin fr.m ⊕ Fin fr.k) (AA I)) p (Sum.inl j) := by
  have hcol : ∀ i, (I.fmat (h : I.Gf) * fr.BA) i (Sum.inl j) = fr.BA i (Sum.inl j) := fun i =>
    congrFun (fix_span h (fun i => fr.B i (Sum.inl j)) (fr.col_span j)) i
  calc fr.MA h p (Sum.inl j) = ∑ i, fr.BiA p i * (I.fmat (h : I.Gf) * fr.BA) i (Sum.inl j) := by
        simp only [Frame.MA, Matrix.mul_assoc]
        rw [Matrix.mul_apply]
    _ = ∑ i, fr.BiA p i * fr.BA i (Sum.inl j) := by simp only [hcol]
    _ = (fr.BiA * fr.BA) p (Sum.inl j) := (Matrix.mul_apply ..).symm
    _ = _ := by rw [fr.BiA_BA]

theorem Frame.MA_11 (h : HfinS I S) : (fr.MA h).toBlocks₁₁ = 1 := by
  ext i j
  simp [Matrix.toBlocks₁₁, fr.MA_inl, Matrix.one_apply]

theorem Frame.MA_21 (h : HfinS I S) : (fr.MA h).toBlocks₂₁ = 0 := by
  ext i j
  simp [Matrix.toBlocks₂₁, fr.MA_inl, Matrix.one_apply]

theorem Frame.MA_unitary (h : HfinS I S) :
    cT (σA I) (fr.MA h) * fr.Jt.map (ιA I) * fr.MA h = fr.Jt.map (ιA I) := by
  have hu : cT (σA I) (I.fmat (h : I.Gf)) * JA I * I.fmat (h : I.Gf) = JA I :=
    (mem_UPts_iff I.J _).1 (h : I.Gf).2
  have hc : cT (σA I) fr.BiA * cT (σA I) fr.BA = 1 := by
    rw [← cT_mulG, fr.BA_BiA, cT_one']
  rw [fr.JtA, Frame.MA, cT_mulG, cT_mulG]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (cT (σA I) fr.BiA) (cT (σA I) fr.BA), hc, Matrix.one_mul,
    ← Matrix.mul_assoc fr.BA fr.BiA, fr.BA_BiA, Matrix.one_mul,
    ← Matrix.mul_assoc (JA I), ← Matrix.mul_assoc (cT (σA I) (I.fmat (h : I.Gf))),
    ← Matrix.mul_assoc (cT (σA I) (I.fmat (h : I.Gf))) (JA I), hu]

def Frame.Y (h : HfinS I S) : Matrix (Fin fr.k) (Fin fr.k) (AA I) := (fr.MA h).toBlocks₂₂

theorem Frame.MA_eq (h : HfinS I S) :
    fr.MA h = Matrix.fromBlocks 1 0 0 (fr.Y h) ∧
      cT (σA I) (fr.Y h) * fr.J'.map (ιA I) * fr.Y h = fr.J'.map (ιA I) := by
  have hJt : IsUnit fr.Jt.det := by
    have hJ : IsUnit I.J.det := isUnit_iff_ne_zero.mpr I.J_det
    apply Matrix.isUnit_det_of_right_inverse (B := fr.Bi * I.J⁻¹ * cT (starRingEnd I.E) fr.Bi)
    rw [Frame.Jt]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc fr.B fr.Bi, fr.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc I.J,
      Matrix.mul_nonsing_inv _ hJ, Matrix.one_mul, ← cT_mulG, fr.inv_mul, cT_one']
  have hdet : fr.Jt.toBlocks₁₁.det ≠ 0 := by
    have h1 := hJt
    rw [fr.Jt_blocks, Matrix.det_fromBlocks_zero₂₁] at h1
    exact (isUnit_of_mul_isUnit_left h1).ne_zero
  have hM : fr.MA h = Matrix.fromBlocks 1 (fr.MA h).toBlocks₁₂ 0 (fr.Y h) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (fr.MA h)]
    rw [fr.MA_11, fr.MA_21, Frame.Y]
  have hU := fr.MA_unitary h
  rw [fr.JtA_blocks, hM, cT_fromBlocks, cT_one', cT_zero', Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at hU
  obtain ⟨-, h12, -, h22⟩ := Matrix.fromBlocks_inj.1 hU
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.mul_one] at h12 h22
  have hX0 : (fr.MA h).toBlocks₁₂ = 0 := unit_cancel fr fr.Jt.toBlocks₁₁ hdet _ h12
  refine ⟨?_, ?_⟩
  · rw [hM, hX0]
  · rw [hX0] at h22
    simpa [cT_zero'] using h22

theorem Frame.MA_mul (h₁ h₂ : HfinS I S) : fr.MA (h₁ * h₂) = fr.MA h₁ * fr.MA h₂ := by
  simp only [Frame.MA, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc fr.BA fr.BiA, fr.BA_BiA, Matrix.one_mul,
    show I.fmat ((h₁ : I.Gf) * (h₂ : I.Gf)) = I.fmat h₁ * I.fmat h₂ from rfl, Matrix.mul_assoc]

theorem Frame.Y_mul (h₁ h₂ : HfinS I S) : fr.Y (h₁ * h₂) = fr.Y h₁ * fr.Y h₂ := by
  show (fr.MA (h₁ * h₂)).toBlocks₂₂ = _
  rw [fr.MA_mul, (fr.MA_eq h₁).1, (fr.MA_eq h₂).1, Matrix.fromBlocks_multiply]
  simp

theorem Frame.Y_one : fr.Y 1 = 1 := by
  have h1 : fr.MA 1 = 1 := by
    simp only [Frame.MA, OneMemClass.coe_one]
    show fr.BiA * (1 : Matrix _ _ (AA I)) * fr.BA = 1
    rw [Matrix.mul_one]
    exact fr.BiA_BA
  ext i j
  simp [Frame.Y, h1, Matrix.toBlocks₂₂, Matrix.one_apply]

def Frame.Yhom : HfinS I S →* Matrix (Fin fr.k) (Fin fr.k) (AA I) where
  toFun := fr.Y
  map_one' := fr.Y_one
  map_mul' := fr.Y_mul

def Frame.Phi : HfinS I S →* UPts I.cm.sig fr.J' (Formalism.MainNotions.S.Af I.F) :=
  fr.Yhom.toHomUnits.codRestrict _ fun h => (fr.MA_eq h).2

def Frame.D (y : Matrix (Fin fr.k) (Fin fr.k) (AA I)) :
    Matrix (Fin fr.m ⊕ Fin fr.k) (Fin fr.m ⊕ Fin fr.k) (AA I) :=
  Matrix.fromBlocks 1 0 0 y

theorem Frame.D_mul (y₁ y₂ : Matrix (Fin fr.k) (Fin fr.k) (AA I)) :
    fr.D (y₁ * y₂) = fr.D y₁ * fr.D y₂ := by
  simp [Frame.D, Matrix.fromBlocks_multiply]

def Frame.P (y : Matrix (Fin fr.k) (Fin fr.k) (AA I)) : Matrix (Fin I.n) (Fin I.n) (AA I) :=
  fr.BA * fr.D y * fr.BiA

theorem Frame.twoPow_mul_twoPow (y₁ y₂ : Matrix (Fin fr.k) (Fin fr.k) (AA I)) :
    fr.P (y₁ * y₂) = fr.P y₁ * fr.P y₂ := by
  simp only [Frame.P, fr.D_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc fr.BiA fr.BA, fr.BiA_BA, Matrix.one_mul]

theorem Frame.P_one : fr.P 1 = 1 := by
  simp only [Frame.P, Frame.D, Matrix.fromBlocks_one, Matrix.mul_one]
  exact fr.BA_BiA

def Frame.Phom : UPts I.cm.sig fr.J' (Formalism.MainNotions.S.Af I.F) →* Matrix (Fin I.n) (Fin I.n) (AA I) where
  toFun y := fr.P ((y : GL (Fin fr.k) (AA I)) : Matrix (Fin fr.k) (Fin fr.k) (AA I))
  map_one' := by simp [fr.P_one]
  map_mul' a b := by simp [fr.twoPow_mul_twoPow]

theorem Frame.P_unitary (y : UPts I.cm.sig fr.J' (Formalism.MainNotions.S.Af I.F)) :
    cT (σA I) (fr.Phom y) * JA I * fr.Phom y = JA I := by
  have hy : cT (σA I) ((y : GL (Fin fr.k) (AA I)) : Matrix (Fin fr.k) (Fin fr.k) (AA I)) *
      fr.J'.map (ιA I) * ((y : GL (Fin fr.k) (AA I)) : Matrix (Fin fr.k) (Fin fr.k) (AA I)) =
      fr.J'.map (ιA I) := y.2
  have hD : cT (σA I) (fr.D ((y : GL (Fin fr.k) (AA I)) : Matrix (Fin fr.k) (Fin fr.k) (AA I))) *
      fr.Jt.map (ιA I) * fr.D ((y : GL (Fin fr.k) (AA I)) : Matrix (Fin fr.k) (Fin fr.k) (AA I)) =
      fr.Jt.map (ιA I) := by
    rw [Frame.D, fr.JtA_blocks, cT_fromBlocks, cT_one', Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp [hy, cT_zero']
  have h1 : cT (σA I) fr.BiA * cT (σA I) fr.BA = 1 := by
    rw [← cT_mulG, fr.BA_BiA, cT_one']
  show cT (σA I) (fr.P _) * JA I * fr.P _ = JA I
  rw [Frame.P, cT_mulG, cT_mulG]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (JA I) fr.BA, ← Matrix.mul_assoc (cT (σA I) fr.BA),
    ← Matrix.mul_assoc (cT (σA I) fr.BA) (JA I) fr.BA, ← fr.JtA,
    ← Matrix.mul_assoc (fr.Jt.map (ιA I)), ← Matrix.mul_assoc (cT (σA I) (fr.D _)),
    ← Matrix.mul_assoc (cT (σA I) (fr.D _)) (fr.Jt.map (ιA I)), hD, fr.JtA]
  simp only [Matrix.mul_assoc]
  rw [fr.BA_BiA, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem Frame.P_fix (y : UPts I.cm.sig fr.J' (Formalism.MainNotions.S.Af I.F)) (s : Fin I.n → I.E) (hs : s ∈ S) :
    fr.Phom y *ᵥ (fun i => ιA I (s i)) = fun i => ιA I (s i) := by
  have h1 : ∀ j, (fr.BiA *ᵥ (fun i => ιA I (s i))) (Sum.inr j) = 0 := by
    intro j
    rw [show (fr.BiA *ᵥ (fun i => ιA I (s i))) (Sum.inr j) = ιA I ((fr.Bi *ᵥ s) (Sum.inr j)) from
      (RingHom.map_mulVec (ιA I) fr.Bi s (Sum.inr j)).symm, fr.S_coord s hs j, map_zero]
  have h2 : fr.D ((y : GL (Fin fr.k) (AA I)) : Matrix (Fin fr.k) (Fin fr.k) (AA I)) *ᵥ
      (fr.BiA *ᵥ (fun i => ιA I (s i))) = fr.BiA *ᵥ (fun i => ιA I (s i)) := by
    rw [Frame.D, Matrix.fromBlocks_mulVec]
    have h3 : (fr.BiA *ᵥ (fun i => ιA I (s i))) ∘ Sum.inr = 0 := funext h1
    rw [h3]
    ext p
    rcases p with i | j <;> simp [h1]
  show (fr.BA * fr.D ((y : GL (Fin fr.k) (AA I)) : Matrix (Fin fr.k) (Fin fr.k) (AA I)) * fr.BiA) *ᵥ
    (fun i => ιA I (s i)) = fun i => ιA I (s i)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_mulVec, fr.BA_BiA,
    Matrix.one_mulVec]

def Frame.PsiG : UPts I.cm.sig fr.J' (Formalism.MainNotions.S.Af I.F) →* I.Gf :=
  fr.Phom.toHomUnits.codRestrict _ fun y => fr.P_unitary y

def Frame.Psi : UPts I.cm.sig fr.J' (Formalism.MainNotions.S.Af I.F) →* HfinS I S :=
  fr.PsiG.codRestrict _ fun y => fun s hs => fr.P_fix y s hs

theorem Frame.fmat_Psi (y : UPts I.cm.sig fr.J' (Formalism.MainNotions.S.Af I.F)) :
    I.fmat ((fr.Psi y : HfinS I S) : I.Gf) =
      fr.P ((y : GL (Fin fr.k) (AA I)) : Matrix (Fin fr.k) (Fin fr.k) (AA I)) := rfl

theorem Frame.Phi_Psi (y : UPts I.cm.sig fr.J' (Formalism.MainNotions.S.Af I.F)) : fr.Phi (fr.Psi y) = y := by
  apply Subtype.ext
  apply Units.ext
  show (fr.BiA * I.fmat ((fr.Psi y : HfinS I S) : I.Gf) * fr.BA).toBlocks₂₂ = _
  rw [fr.fmat_Psi y]
  simp only [Frame.P, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc fr.BiA fr.BA, fr.BiA_BA, Matrix.one_mul, Matrix.mul_one]
  simp [Frame.D]

theorem Frame.Psi_Phi (h : HfinS I S) : fr.Psi (fr.Phi h) = h := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  show I.fmat ((fr.Psi (fr.Phi h) : HfinS I S) : I.Gf) = I.fmat (h : I.Gf)
  rw [fr.fmat_Psi]
  show fr.BA * Matrix.fromBlocks 1 0 0 (fr.Y h) * fr.BiA = _
  rw [← (fr.MA_eq h).1, Frame.MA]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc fr.BA fr.BiA, fr.BA_BiA, Matrix.one_mul, Matrix.mul_one]

def Frame.iso : HfinS I S ≃* UPts I.cm.sig fr.J' (Formalism.MainNotions.S.Af I.F) where
  toFun := fr.Phi
  invFun := fr.Psi
  left_inv := fr.Psi_Phi
  right_inv := fr.Phi_Psi
  map_mul' := fr.Phi.map_mul

end Frame

theorem frameIso : FrameIso := by
  intro I S fr
  exact ⟨fr.iso, fun y => fr.fmat_Psi y⟩

end PI.UnitaryGroupMassFormula.InHHClassFin
