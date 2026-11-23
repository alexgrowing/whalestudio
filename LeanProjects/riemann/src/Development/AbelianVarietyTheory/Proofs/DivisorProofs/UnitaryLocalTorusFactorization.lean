import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeviElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementTorusPart

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.PlaneLeviAt

open GlobalTheory.PlaneLeviExt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def dg (σ : E →ₐ[F] E) (t : (AE F E)ˣ) : Matrix (Fin 2) (Fin 2) (AE F E) :=
  Matrix.diagonal ![t.1, cA σ (t⁻¹).1]

def blkT {d₁ : ℕ} (σ : E →ₐ[F] E) (t : (AE F E)ˣ) (g : Matrix (Fin d₁) (Fin d₁) (AE F E)) :
    Matrix (Fin d₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E) :=
  Matrix.fromBlocks g 0 0 (dg σ t)

lemma dg_mul (σ : E →ₐ[F] E) (t t' : (AE F E)ˣ) : dg σ t * dg σ t' = dg σ (t * t') := by
  rw [dg, dg, dg, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i; fin_cases i
  · simp
  · simp [← map_mul, mul_comm]

lemma dg_one (σ : E →ₐ[F] E) : dg σ (1 : (AE F E)ˣ) = 1 := by
  rw [dg, ← Matrix.diagonal_one]
  congr 1
  funext i; fin_cases i <;> simp

lemma blkT_mul {d₁ : ℕ} (σ : E →ₐ[F] E) (t t' : (AE F E)ˣ) (g g' : Matrix (Fin d₁) (Fin d₁) (AE F E)) :
    blkT σ t g * blkT σ t' g' = blkT σ (t * t') (g * g') := by
  simp [blkT, Matrix.fromBlocks_multiply, dg_mul]

lemma blkT_one {d₁ : ℕ} (σ : E →ₐ[F] E) : blkT σ (1 : (AE F E)ˣ) (1 : Matrix (Fin d₁) (Fin d₁) (AE F E)) = 1 := by
  rw [blkT, dg_one, Matrix.fromBlocks_one]

def leviT {d d₁ : ℕ} (σ : E →ₐ[F] E) (hd : d = d₁ + 2) (H' : Plane E d d₁) (t : (AE F E)ˣ)
    (g : Matrix (Fin d₁) (Fin d₁) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E) :=
  incM F (frame H') * blkT σ t g * incM F (coframe hd H')

section
variable {d d₁ : ℕ} {hd : d = d₁ + 2} {H' : Plane E d d₁}

lemma leviT_mul (σ : E →ₐ[F] E) (hu : IsUnit (sq hd H')) (t t' : (AE F E)ˣ) (g g' : Matrix (Fin d₁) (Fin d₁) (AE F E)) :
    leviT σ hd H' t g * leviT σ hd H' t' g' = leviT σ hd H' (t * t') (g * g') := by
  simp only [leviT, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F (coframe hd H')), T_S hu, Matrix.one_mul, ← Matrix.mul_assoc (blkT σ t g), blkT_mul]

lemma leviT_one (σ : E →ₐ[F] E) (hu : IsUnit (sq hd H')) : leviT σ hd H' 1 (1 : Matrix (Fin d₁) (Fin d₁) (AE F E)) = 1 := by
  rw [leviT, blkT_one, Matrix.mul_one, S_T hu]

lemma leviT_frame (σ : E →ₐ[F] E) (hu : IsUnit (sq hd H')) (t : (AE F E)ˣ) (g : Matrix (Fin d₁) (Fin d₁) (AE F E)) :
    leviT σ hd H' t g * incM F (frame H') = incM F (frame H') * blkT σ t g := by
  rw [leviT, Matrix.mul_assoc, T_S hu, Matrix.mul_one]

end

end GlobalTheory.PlaneLeviAt

namespace GlobalTheory.PlaneLeviAt

open GlobalTheory.PlaneLeviExt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

lemma dg_unitary (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (t : (AE F E)ˣ) :
    (dg σ t)ᵀ * incM F (hyp (E := E)) * (dg σ t).map (cA σ) = incM F (hyp (E := E)) := by
  have hc := GlobalTheory.AdelicPlaneLevi.cA_cA σ hσ
  have e1 : t.1 * (t⁻¹).1 = 1 := t.mul_inv
  have e2 : cA σ (t⁻¹).1 * cA σ t.1 = 1 := by rw [← map_mul, t.inv_mul, map_one]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dg, hyp, incM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hc, e1, e2]

variable {d d₁ : ℕ} {hd : d = d₁ + 2} {H' : Plane E d d₁}

lemma leviT_unitary (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {W : Spc F E d}
    {W₁ : Spc F E d₁} {i₀ i₁ r' s' : ℕ} (hW : W.IsSkew σ B r' s') (hA : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hu : IsUnit (sq hd H')) (t : (AE F E)ˣ) (g : Matrix (Fin d₁) (Fin d₁) (AE F E))
    (hg : gᵀ * incM F W₁.J * g.map (cA σ) = incM F W₁.J) :
    (leviT σ hd H' t g)ᵀ * incM F W.J * (leviT σ hd H' t g).map (cA σ) = incM F W.J := by
  have hmap : ∀ {a b c : Type} [Fintype b] (X : Matrix a b (AE F E)) (Y : Matrix b c (AE F E)),
      (X * Y).map (cA σ) = X.map (cA σ) * Y.map (cA σ) := fun X Y => Matrix.map_mul (f := (cA σ).toRingHom)
  have hG : (incM F (frame H'))ᵀ * incM F W.J * (incM F (frame H')).map (cA σ) =
      incM F (Matrix.fromBlocks W₁.J 0 0 hyp) := by
    rw [← gram_frame σ hσ B hW hA, incM_mul, incM_mul, incM_transpose, cA_incM]
  have hJ : incM F W.J = (incM F (coframe hd H'))ᵀ * incM F (Matrix.fromBlocks W₁.J 0 0 hyp) *
      (incM F (coframe hd H')).map (cA σ) := by
    have h1 : (incM F (frame H') * incM F (coframe hd H'))ᵀ * incM F W.J *
        (incM F (frame H') * incM F (coframe hd H')).map (cA σ) = incM F W.J := by
      rw [S_T hu, Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
    calc incM F W.J = (incM F (frame H') * incM F (coframe hd H'))ᵀ * incM F W.J *
          (incM F (frame H') * incM F (coframe hd H')).map (cA σ) := h1.symm
      _ = (incM F (coframe hd H'))ᵀ * ((incM F (frame H'))ᵀ * incM F W.J * (incM F (frame H')).map (cA σ)) *
          (incM F (coframe hd H')).map (cA σ) := by
        rw [Matrix.transpose_mul, hmap]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hG]
  have hB : (blkT σ t g)ᵀ * incM F (Matrix.fromBlocks W₁.J 0 0 hyp) * (blkT σ t g).map (cA σ) =
      incM F (Matrix.fromBlocks W₁.J 0 0 hyp) := by
    have e1 : incM F (Matrix.fromBlocks W₁.J 0 0 hyp) = Matrix.fromBlocks (incM F W₁.J) 0 0 (incM F hyp) := by
      simp [incM, Matrix.fromBlocks_map]
    have e2 : (blkT σ t g).map (cA σ) = Matrix.fromBlocks (g.map (cA σ)) 0 0 ((dg σ t).map (cA σ)) := by
      rw [blkT, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
    rw [e1, e2, blkT, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [hg, dg_unitary σ hσ t]
  calc (leviT σ hd H' t g)ᵀ * incM F W.J * (leviT σ hd H' t g).map (cA σ)
      = (incM F (coframe hd H'))ᵀ * ((blkT σ t g)ᵀ * ((incM F (frame H'))ᵀ * incM F W.J *
          (incM F (frame H')).map (cA σ)) * (blkT σ t g).map (cA σ)) * (incM F (coframe hd H')).map (cA σ) := by
        simp only [leviT, Matrix.transpose_mul, hmap, Matrix.mul_assoc]
    _ = incM F W.J := by rw [hG, hB, ← hJ]

lemma leviT_cols (σ : E →ₐ[F] E) (m : Matrix (Fin d) (Fin d) (AE F E)) (t : (AE F E)ˣ) (g : Matrix (Fin d₁) (Fin d₁) (AE F E))
    (h : m * incM F (frame H') = incM F (frame H') * blkT σ t g) :
    m *ᵥ incV F H'.x = t.1 • incV F H'.x ∧ m *ᵥ incV F H'.y = cA σ (t⁻¹).1 • incV F H'.y ∧
      m * incM F H'.ι = incM F H'.ι * g := by
  rw [incM_frame, Matrix.mul_fromCols, blkT, Matrix.fromCols_mul_fromBlocks] at h
  simp only [Matrix.mul_zero, add_zero, zero_add] at h
  obtain ⟨h1, h2⟩ := Matrix.fromCols_inj.eq_iff.mp h
  refine ⟨?_, ?_, h1⟩
  · funext i
    have := congrFun (congrFun h2 i) 0
    simp only [Matrix.mul_diagonal, dg] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, twoCols, incM, incV, mul_comm] using this
  · funext i
    have := congrFun (congrFun h2 i) 1
    simp only [Matrix.mul_diagonal, dg] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, twoCols, incM, incV, mul_comm] using this

end GlobalTheory.PlaneLeviAt

namespace GlobalTheory.PlaneLeviAt

open GlobalTheory.PlaneLeviExt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

lemma at_mul {R : Type} [Zero R] (ev : AF F → R) {a b c : Type} [Fintype b] [Fintype c]
    (S : Matrix a b (AE F E)) (X : Matrix b c (AE F E)) (T : Matrix c a (AE F E)) (hX : At ev X) :
    At ev (S * X * T) := by
  intro u hu
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hX u hu, Matrix.mul_zero, Matrix.zero_mul]

lemma at_blkT {R : Type} [Zero R] (ev : AF F → R) (σ : E →ₐ[F] E) {d₁ : ℕ} (t : (AE F E)ˣ)
    (g : Matrix (Fin d₁) (Fin d₁) (AE F E)) (ht : At ev (t.1 - 1)) (hg : At ev (g - 1)) :
    At ev (blkT σ t g - 1) := by
  intro u hu
  have h1 : u • (t.1 - 1) = 0 := ht u hu
  have h2 : u • (cA σ (t⁻¹).1 - 1) = 0 := by
    have e : cA σ (t⁻¹).1 - 1 = cA σ (-((t⁻¹).1 * (t.1 - 1))) := by
      rw [map_neg, mul_sub, t.inv_mul, mul_one, map_sub, map_one]; ring
    rw [e, ← map_smul, smul_neg, ← mul_smul_comm, h1, mul_zero, neg_zero, map_zero]
  have h3 : ∀ k l, u • (g - 1) k l = 0 := fun k l => by
    have := congrFun (congrFun (hg u hu) k) l
    simpa using this
  ext (k | k) (l | l)
  · simpa [blkT, Matrix.one_apply] using h3 k l
  · simp [blkT, Matrix.one_apply]
  · simp [blkT, Matrix.one_apply]
  · fin_cases k <;> fin_cases l
    · simpa [blkT, dg, Matrix.one_apply] using h1
    · simp [blkT, dg, Matrix.one_apply]
    · simp [blkT, dg, Matrix.one_apply]
    · simpa [blkT, dg, Matrix.one_apply] using h2

theorem exists_isLevi_at : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ),
    B.IsGood σ → W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (v : Pl F) (t : (AE F E)ˣ), At (F := F) (evFin F v) (t.1 - 1) → ∀ h₁ : UA σ W₁.J, h₁ ∈ UAt σ W₁ (evFin F v) →
      ∃ m : UA σ W.J, IsLevi H' t h₁ m ∧ m ∈ UAt σ W (evFin F v) := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hA v t ht h₁ hh₁
  have hσ : ∀ z, σ (σ z) = z := GlobalTheory.AdelicPlaneLevi.sigma_invol hB.cm
  have hu := isUnit_sq σ hσ B hW hW₁ hA
  have hinv : mat h₁ * mat h₁⁻¹ = 1 := by
    show ((h₁.1 * (h₁⁻¹).1 : GL (Fin d₁) (AE F E)) : Matrix (Fin d₁) (Fin d₁) (AE F E)) = 1
    rw [← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have hinv' : mat h₁⁻¹ * mat h₁ = 1 := by
    show (((h₁⁻¹).1 * h₁.1 : GL (Fin d₁) (AE F E)) : Matrix (Fin d₁) (Fin d₁) (AE F E)) = 1
    rw [← Subgroup.coe_mul, inv_mul_cancel]; rfl
  let mU : GL (Fin d) (AE F E) := ⟨leviT σ hA.rank H' t (mat h₁), leviT σ hA.rank H' t⁻¹ (mat h₁⁻¹),
    by rw [leviT_mul σ hu, hinv, mul_inv_cancel, leviT_one σ hu],
    by rw [leviT_mul σ hu, hinv', inv_mul_cancel, leviT_one σ hu]⟩
  have hmem : mU ∈ UG (cA σ) (incM F W.J) := leviT_unitary σ hσ B hW hA hu t (mat h₁) h₁.2
  refine ⟨⟨mU, hmem⟩, leviT_cols σ _ t (mat h₁) (leviT_frame σ hu t (mat h₁)), ?_⟩
  show At (evFin F v) (leviT σ hA.rank H' t (mat h₁) - 1)
  have e : leviT σ hA.rank H' t (mat h₁) - 1 =
      incM F (frame H') * (blkT σ t (mat h₁) - 1) * incM F (coframe hA.rank H') := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, S_T hu]; rfl
  rw [e]
  exact at_mul _ _ _ _ (at_blkT _ σ t _ ht hh₁)

end GlobalTheory.PlaneLeviAt
