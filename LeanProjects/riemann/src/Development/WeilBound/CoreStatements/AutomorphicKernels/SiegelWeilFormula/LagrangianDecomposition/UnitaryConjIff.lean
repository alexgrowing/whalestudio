import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.LdExOfLeaves
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.BlockIndexInrLast

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem unitary_conj_iff {S ι : Type*} [CommRing S] [Fintype ι] [DecidableEq ι] (c : S →+* S) (D J P Q X : Matrix ι ι S)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (hG : Pᵀ * D * P.map c = J) :
    Xᵀ * D * X.map c = D ↔ (Q * X * P)ᵀ * J * (Q * X * P).map c = J := by
  have t1 : Qᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hPQ, Matrix.transpose_one]
  have t2 : Pᵀ * Qᵀ = 1 := by rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one]
  have m1 : P.map c * Q.map c = 1 := by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero c) (map_one c)]
  have m2 : Q.map c * P.map c = 1 := by rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero c) (map_one c)]
  have hD : D = Qᵀ * J * Q.map c := by
    rw [← hG]
    calc D = (Qᵀ * Pᵀ) * D * (P.map c * Q.map c) := by rw [t1, m1, Matrix.one_mul, Matrix.mul_one]
      _ = Qᵀ * (Pᵀ * D * P.map c) * Q.map c := by simp only [Matrix.mul_assoc]
  constructor
  · intro hX
    rw [← hG]
    calc (Q * X * P)ᵀ * (Pᵀ * D * P.map c) * (Q * X * P).map c
        = Pᵀ * (Xᵀ * ((Qᵀ * Pᵀ) * D * (P.map c * Q.map c)) * X.map c) * P.map c := by
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = Pᵀ * D * P.map c := by rw [t1, m1, Matrix.one_mul, Matrix.mul_one, hX]
  · intro hY
    have hX : X = P * (Q * X * P) * Q := by
      calc X = (P * Q) * X * (P * Q) := by rw [hPQ, Matrix.one_mul, Matrix.mul_one]
        _ = P * (Q * X * P) * Q := by simp only [Matrix.mul_assoc]
    generalize Q * X * P = Y at hX hY
    rw [hX, hD]
    calc (P * Y * Q)ᵀ * (Qᵀ * J * Q.map c) * (P * Y * Q).map c
        = Qᵀ * (Yᵀ * ((Pᵀ * Qᵀ) * J * (Q.map c * P.map c)) * Y.map c) * Q.map c := by
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = Qᵀ * J * Q.map c := by rw [t2, m2, Matrix.one_mul, Matrix.mul_one, hY]

theorem blk_out {R : Type*} [Semiring R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    ∀ u ∈ ({Sum.inl (i0 h), Sum.inr (i0 h)} : Set (Fin N ⊕ Fin N)), ∀ v,
      blk h M 1 u v = (1 : Matrix _ _ R) u v ∧ blk h M 1 v u = (1 : Matrix _ _ R) v u := by
  intro u hu v
  obtain ⟨p, hp⟩ := eB_out h u hu
  have e1 : (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) R) = blk h 1 1 := (blk_one h).symm
  rw [e1, blk_apply, blk_apply, blk_apply, blk_apply, hp]
  generalize eB h v = x
  rcases x with x | x <;> simp

def blkHom {S : Type*} [Semiring S] {N n : ℕ} (h : n + 1 = N) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) S →* Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) S where
  toFun M := blk h M 1
  map_one' := blk_one h
  map_mul' M M' := by rw [blk_mul, Matrix.one_mul]

def blkGL {S : Type*} [Semiring S] {N n : ℕ} (h : n + 1 = N) :
    GL (Fin n ⊕ Fin n) S →* GL (Fin N ⊕ Fin N) S := Units.map (blkHom h)

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def bA {ι : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) : GL ι (AE F E) :=
  Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) b

theorem bA_val {ι : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) : (bA (F := F) b).1 = incM F b.1 := rfl

theorem bA_inv_val {ι : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) : ((bA (F := F) b)⁻¹).1 = incM F (b⁻¹).1 := by
  rw [bA, ← map_inv]
  rfl

theorem incM_mul_inv {ι : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) : incM F b.1 * incM F (b⁻¹).1 = 1 := by
  rw [← bA_inv_val b, ← bA_val (F := F) b, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem incM_inv_mul {ι : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) : incM F (b⁻¹).1 * incM F b.1 = 1 := by
  rw [← bA_inv_val b, ← bA_val (F := F) b, ← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem cA_incl (z : E) : cA σ (inclR (F := F) (AF F) z) = inclR (F := F) (AF F) (σ z) := by
  simp [cA, inclR]

theorem incM_gram {ι : Type} [Fintype ι] [DecidableEq ι] (P D : Matrix ι ι E) :
    (incM F P)ᵀ * incM F D * (incM F P).map (cA σ) = incM F (Pᵀ * D * P.map σ) := by
  have e : (incM F P).map (cA σ) = incM F (P.map σ) := by
    ext i j
    simp [incM, cA_incl]
  rw [e, incM, incM, incM, incM, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

theorem incM_dbl {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι E) : incM F (dbl J) = dbl (incM F J) := by
  ext u v
  rcases u with u | u <;> rcases v with v | v <;> simp [incM, dbl]

theorem incM_jeps (k : ℕ) (ε : ℤˣ) : incM F (jeps k ε : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) E) =
    Matrix.fromBlocks 0 1 ((inclR (F := F) (AF F) ((ε : ℤ) : E)) • 1) 0 := by
  ext u v
  rcases u with u | u <;> rcases v with v | v <;> simp [incM, jeps, Matrix.one_apply] <;> split_ifs <;> simp

def jHom (d : SD σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) :
    G2 σ Y →* GL (Fin d.n ⊕ Fin d.n) (AE F E) :=
  (MulAut.conj (bA d.b)).toMonoidHom.comp ((blkGL h).comp
    ((MulAut.conj (bA (F := F) b)⁻¹).toMonoidHom.comp (UG (cA σ) (dbl (incM F Y.J))).subtype))

theorem inFrame_eq {n : ℕ} {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (g : G2 σ Y) :
    inFrame b g = incM F (b⁻¹).1 * g.1.1 * incM F b.1 := rfl

theorem jHom_val (d : SD σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (g : G2 σ Y) :
    (jHom d h b g).1 = incM F d.b.1 * blk h (inFrame b g) 1 * incM F (d.b⁻¹).1 := by
  simp only [jHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype,
    Units.val_mul, bA_val, bA_inv_val, blkGL, Units.coe_map, blkHom, MonoidHom.coe_mk, OneHom.coe_mk, inFrame_eq]

theorem jHom_mem (d : SD σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ)
    (e1 : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε) (e2 : b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε) (g : G2 σ Y) :
    jHom d h b g ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
  have hG1 : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom = incM F (jeps d.n ε) := by
    rw [← e1, ← incM_gram, incM_dbl]; rfl
  have hG2 : (incM F b.1)ᵀ * dbl (incM F Y.J) * (incM F b.1).map (cA σ).toRingHom = incM F (jeps n ε) := by
    rw [← e2, ← incM_gram, incM_dbl]; rfl
  have hg : (g.1.1)ᵀ * dbl (incM F Y.J) * (g.1.1).map (cA σ).toRingHom = dbl (incM F Y.J) := g.2
  have hM := (unitary_conj_iff (cA σ).toRingHom _ _ _ _ g.1.1 (incM_mul_inv b) (incM_inv_mul b) hG2).1 hg
  rw [← inFrame_eq] at hM
  show (jHom d h b g).1ᵀ * dbl (incM F d.Y.J) * (jHom d h b g).1.map (cA σ).toRingHom = dbl (incM F d.Y.J)
  rw [unitary_conj_iff (cA σ).toRingHom _ _ _ _ _ (incM_mul_inv d.b) (incM_inv_mul d.b) hG1, jHom_val]
  have eQP : incM F (d.b⁻¹).1 * (incM F d.b.1 * blk h (inFrame b g) 1 * incM F (d.b⁻¹).1) * incM F d.b.1 =
      blk h (inFrame b g) 1 := by
    simp only [← Matrix.mul_assoc, incM_inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, incM_inv_mul, Matrix.mul_one]
  rw [eQP, incM_jeps, jepsR_blk h, ← incM_jeps, ← incM_jeps, blk_transpose, blk_map _ _ _ _ (map_zero _), blk_mul,
    blk_mul, hM]
  congr 1
  simp [Matrix.map_one _ (map_zero _) (map_one _)]

end PositivityTheory.SiegelWeilFormula.Ald

end
