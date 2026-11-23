import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScal

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev UD (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) : Type := UG (cA σ) (dbl (incM F J))

def UDAt {R : Type} [Zero R] (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (ev : AF F → R) : Set (UD σ J) :=
  {p | At ev (((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) - 1)}

def dsum {k : Type} [CommRing k] {d : ℕ} (c : GL (Fin d) k) : GL (Fin d ⊕ Fin d) k where
  val := Matrix.fromBlocks c.val 0 0 c.val
  inv := Matrix.fromBlocks (c⁻¹).val 0 0 (c⁻¹).val
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

def locMatD {σ : E →ₐ[F] E} {v : Pl F} (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (c : GL (Fin d) (Fv F v)) : UD σ J →* GL (Fin d ⊕ Fin d) (Fv F v) where
  toFun p := (dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) p.1 * dsum c
  map_one' := by simp
  map_mul' p q := by simp [mul_assoc]

abbrev DblCo (σ : E →ₐ[F] E) {n d : ℕ} (X : Spc F E n) (W : Spc F E d) : Type :=
  Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d)

abbrev DblRep (σ : E →ₐ[F] E) {n d : ℕ} (W : Spc F E d) : Type :=
  UD σ W.J →* Module.End ℂ ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ)

structure IsLinD {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (ψ : AddChar (AF F) ℂ) (dd : DblCo σ X W)
    {v : Pl F} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (ιd : ((Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) → ℂ)) :
    Prop where
  bij : Set.BijOn ιd (SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) : Set _)
    (SB (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) : Set _)
  trans : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) u → u.map (piW (t.comp σ)) = 0 →
    ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
      Acts (evFin F v) (dd.rho ψ u) φ φ₁ →
      ∀ Y, ιd φ₁ Y = ιd φ (Y + (b⁻¹).val * u.map (piW t) * ((dsum c)⁻¹).valᵀ)
  mult : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) u → u.map (piW t) = 0 →
    ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
      Acts (evFin F v) (dd.rho ψ u) φ φ₁ →
      ∀ x : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
        ιd φ₁ ((b⁻¹).val * x.map (piW t) * ((dsum c)⁻¹).valᵀ) =
          ψ (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) x u) * ιd φ ((b⁻¹).val * x.map (piW t) * ((dsum c)⁻¹).valᵀ)

def LocOps {σ : E →ₐ[F] E} {n d : ℕ} {W : Spc F E d} (omd : DblRep σ (n := n) W) (v : Pl F) : Prop :=
  ∀ p ∈ UDAt σ W.J (evFin F v), ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
    ∃ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (omd p) φ φ₁

def IsShapeD {σ : E →ₐ[F] E} {n d : ℕ} {W : Spc F E d} (omd : DblRep σ (n := n) W) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (c : GL (Fin d) (Fv F v))
    (ιd : ((Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) → ℂ))
    (cd : UD σ W.J → ℂ) : Prop :=
  ∀ p ∈ UDAt σ W.J (evFin F v), ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
    ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (omd p) φ φ₁ →
      ιd φ₁ = cd p • fun Y => ιd φ (Y * (GlobalTheory.SplitFlip.invT (locMatD t c p)).val)

theorem exists_diag_one {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (h : UA σ J) :
    ∃ gd : UD σ J, ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
      Matrix.fromBlocks (mat h) 0 0 1 := by
  let A : Matrix (Fin d) (Fin d) (AE F E) := mat h
  let Ai : Matrix (Fin d) (Fin d) (AE F E) := (((h : GL (Fin d) (AE F E))⁻¹ : GL (Fin d) (AE F E)) : Matrix _ _ _)
  have h1 : A * Ai = 1 := (h : GL (Fin d) (AE F E)).mul_inv
  have h2 : Ai * A = 1 := (h : GL (Fin d) (AE F E)).inv_mul
  let G : GL (Fin d ⊕ Fin d) (AE F E) :=
    ⟨Matrix.fromBlocks A 0 0 1, Matrix.fromBlocks Ai 0 0 1, by simp [fromBlocks_multiply, h1],
      by simp [fromBlocks_multiply, h2]⟩
  have hu : Aᵀ * incM F J * A.map (cA σ) = incM F J := h.2
  refine ⟨⟨G, ?_⟩, rfl⟩
  show (Matrix.fromBlocks A 0 0 1)ᵀ * dbl (incM F J) * (Matrix.fromBlocks A 0 0 1).map (cA σ) = dbl (incM F J)
  rw [fromBlocks_transpose, fromBlocks_map, dbl, fromBlocks_multiply, fromBlocks_multiply]
  simp only [transpose_zero, transpose_one, Matrix.map_zero _ (map_zero (cA σ)), Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ)),
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, hu]

theorem gdet_locMatD_diag {σ : E →ₐ[F] E} {v : Pl F} (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (c : GL (Fin d) (Fv F v)) (h : UA σ J) (gd : UD σ J)
    (hgd : ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
      Matrix.fromBlocks (mat h) 0 0 1) :
    GlobalTheory.SplitFlip.gdet (locMatD t c gd) = GlobalTheory.SplitFlip.gdet (locMat t c h) := by
  apply Units.ext
  have e : (locMatD t c gd).val =
      Matrix.fromBlocks (locMat t c h).val 0 0 1 := by
    show ((dsum c)⁻¹).val * (((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix _ _ _).map (piW t)) * (dsum c).val = _
    rw [hgd, locMat_val, fromBlocks_map]
    simp only [dsum, Units.inv_mk, fromBlocks_multiply, Matrix.map_zero _ (map_zero (piW t)),
      Matrix.map_one _ (map_zero (piW t)) (map_one (piW t)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.mul_one, Matrix.one_mul]
    congr 1
    simp [Units.mul_inv]
  simp only [GlobalTheory.SplitFlip.gdet, Matrix.GeneralLinearGroup.val_det_apply, e, det_fromBlocks_zero₂₁, det_one, mul_one]

def fixDiag {k : Type} [CommRing k] {d : ℕ} (A : GL (Fin d) k) : GL (Fin d ⊕ Fin d) k where
  val := Matrix.fromBlocks A.val (1 - A.val) 0 1
  inv := Matrix.fromBlocks (A⁻¹).val (1 - (A⁻¹).val) 0 1
  val_inv := by simp [fromBlocks_multiply, Matrix.mul_sub]
  inv_val := by simp [fromBlocks_multiply, Matrix.mul_sub]

theorem fixDiag_diag {k : Type} [CommRing k] {d : ℕ} (A : GL (Fin d) k) :
    ((fixDiag A).val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) k) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) k) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) k) * (1 : Matrix (Fin d) (Fin d) k) := by
  simp only [fixDiag, diagCols, Matrix.mul_one]
  rw [← fromCols_fromRows_eq_fromBlocks, fromCols_mul_fromRows, fromRows_mul, fromRows_mul]
  ext (i | i) j <;> simp

theorem gdet_fixDiag {k : Type} [Field k] {d : ℕ} (A : GL (Fin d) k) :
    GlobalTheory.SplitFlip.gdet (fixDiag A) = GlobalTheory.SplitFlip.gdet A := by
  apply Units.ext
  simp [GlobalTheory.SplitFlip.gdet, Matrix.GeneralLinearGroup.val_det_apply, fixDiag, det_fromBlocks_zero₂₁]

theorem fromBlocks_sub_one {R : Type} [CommRing R] {d : ℕ} (A : Matrix (Fin d) (Fin d) R) :
    Matrix.fromBlocks A (0 : Matrix (Fin d) (Fin d) R) 0 (1 : Matrix (Fin d) (Fin d) R) - 1 =
      Matrix.fromBlocks (A - 1) (0 : Matrix (Fin d) (Fin d) R) 0 0 := by
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

end GlobalTheory.DblScal

end
