import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertDbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev UD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : Type := UG (cA σ) (dbl (incM F W.J))

def matD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
  g.1.1

def latAtD {d : ℕ} (W : Spc F E d) (v : Pl F) : Set (Fin d ⊕ Fin d → AE F E) :=
  {z | (fun i => z (Sum.inl i)) ∈ GlobalTheory.InertSph.latAt W v ∧ (fun i => z (Sum.inr i)) ∈ GlobalTheory.InertSph.latAt W v}

def KAtD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) : Set (UD σ W) :=
  {g | At (evFin F v) (matD g - 1) ∧
    ∀ z ∈ latAtD W v, matD g *ᵥ z ∈ latAtD W v ∧ matD g⁻¹ *ᵥ z ∈ latAtD W v}

def antiCols (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := Matrix.fromRows 1 (-1)

def ParD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) : Set (UD σ W) :=
  {p | p ∈ KAtD σ W v ∧ ∃ t : GL (Fin d) (AE F E), matD p * diagCols (Fin d) = diagCols (Fin d) * (t : Matrix (Fin d) (Fin d) (AE F E))}

def NabD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) : Set (UD σ W) :=
  {n | n ∈ KAtD σ W v ∧ matD n * antiCols d = antiCols d ∧
    ∃ b : Matrix (Fin d) (Fin d) (AE F E), matD n * diagCols (Fin d) = diagCols (Fin d) + antiCols d * b}

theorem fromBlocks_mem {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (k : UA σ W.J) :
    ((Matrix.fromBlocks (mat k) 0 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)))ᵀ * dbl (incM F W.J) *
      (Matrix.fromBlocks (mat k) 0 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F W.J) := by
  have hk : (mat k)ᵀ * incM F W.J * (mat k).map (cA σ) = incM F W.J := k.2
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, dbl, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hk, Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]

def inlD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : UA σ W.J →* UD σ W where
  toFun k := ⟨⟨Matrix.fromBlocks (mat k) 0 0 1, Matrix.fromBlocks (mat k⁻¹) 0 0 1,
      by rw [Matrix.fromBlocks_multiply]; simp [mat, ← Matrix.GeneralLinearGroup.coe_mul, Matrix.fromBlocks_one],
      by rw [Matrix.fromBlocks_multiply]; simp [mat, ← Matrix.GeneralLinearGroup.coe_mul, Matrix.fromBlocks_one]⟩,
    fromBlocks_mem k⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    show Matrix.fromBlocks (mat (1 : UA σ W.J)) 0 0 1 = 1
    simp [mat, Matrix.fromBlocks_one]
  map_mul' a b := by
    apply Subtype.ext; apply Units.ext
    show Matrix.fromBlocks (mat (a * b)) 0 0 1 = Matrix.fromBlocks (mat a) 0 0 1 * Matrix.fromBlocks (mat b) 0 0 1
    rw [Matrix.fromBlocks_multiply]; simp [mat]

theorem matD_inlD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (k : UA σ W.J) :
    matD (inlD σ W k) = Matrix.fromBlocks (mat k) 0 0 1 := rfl

def dblFun {κ : Type} (Ψ : (κ → AF F) → ℂ) : (κ ⊕ κ → AF F) → ℂ := boxFun Ψ fun x => star (Ψ x)

end GlobalTheory.InertDbl

end
