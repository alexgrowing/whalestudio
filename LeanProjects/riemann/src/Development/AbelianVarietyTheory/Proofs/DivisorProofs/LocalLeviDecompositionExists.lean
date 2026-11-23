import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeviElement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.PlaneLeviUnit

open GlobalTheory.PlaneLeviExt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {d d₁ : ℕ}

lemma cA_cA (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

def dg (a b : AE F E) (g : Matrix (Fin d₁) (Fin d₁) (AE F E)) :
    Matrix (Fin d₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E) :=
  Matrix.fromBlocks g 0 0 (Matrix.diagonal ![a, b])

lemma dg_mul (a b a' b' : AE F E) (g g' : Matrix (Fin d₁) (Fin d₁) (AE F E)) :
    dg a b g * dg a' b' g' = dg (a * a') (b * b') (g * g') := by
  simp only [dg, Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add]
  congr 2
  ext i; fin_cases i <;> rfl

lemma dg_one : dg (1 : AE F E) 1 (1 : Matrix (Fin d₁) (Fin d₁) (AE F E)) = 1 := by
  rw [dg, ← Matrix.fromBlocks_one]
  congr 1
  rw [← Matrix.diagonal_one]
  congr 1
  ext i; fin_cases i <;> rfl

variable {hd : d = d₁ + 2} {H' : Plane E d d₁}

def mM (hd : d = d₁ + 2) (H' : Plane E d d₁) (a b : AE F E) (g : Matrix (Fin d₁) (Fin d₁) (AE F E)) :
    Matrix (Fin d) (Fin d) (AE F E) :=
  incM F (frame H') * dg a b g * incM F (coframe hd H')

lemma mM_mul (hu : IsUnit (sq hd H')) (a b a' b' : AE F E) (g g' : Matrix (Fin d₁) (Fin d₁) (AE F E)) :
    mM (F := F) hd H' a b g * mM hd H' a' b' g' = mM hd H' (a * a') (b * b') (g * g') := by
  simp only [mM, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F (coframe hd H')), T_S hu, Matrix.one_mul, ← Matrix.mul_assoc (dg a b g), dg_mul]

lemma mM_one (hu : IsUnit (sq hd H')) : mM (F := F) hd H' 1 1 1 = 1 := by
  rw [mM, dg_one, Matrix.mul_one, S_T hu]

lemma mM_frame (hu : IsUnit (sq hd H')) (a b : AE F E) (g : Matrix (Fin d₁) (Fin d₁) (AE F E)) :
    mM hd H' a b g * incM F (frame H') = incM F (frame H') * dg a b g := by
  rw [mM, Matrix.mul_assoc, T_S hu, Matrix.mul_one]

lemma conj_unitary (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {W : Spc F E d}
    {W₁ : Spc F E d₁} {i₀ i₁ r' s' : ℕ} (hW : W.IsSkew σ B r' s') (hA : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hu : IsUnit (sq hd H')) (D : Matrix (Fin d₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E))
    (hD : Dᵀ * incM F (Matrix.fromBlocks W₁.J 0 0 hyp) * D.map (cA σ) = incM F (Matrix.fromBlocks W₁.J 0 0 hyp)) :
    (incM F (frame H') * D * incM F (coframe hd H'))ᵀ * incM F W.J *
      (incM F (frame H') * D * incM F (coframe hd H')).map (cA σ) = incM F W.J := by
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
  calc (incM F (frame H') * D * incM F (coframe hd H'))ᵀ * incM F W.J *
        (incM F (frame H') * D * incM F (coframe hd H')).map (cA σ)
      = (incM F (coframe hd H'))ᵀ * (Dᵀ * ((incM F (frame H'))ᵀ * incM F W.J *
          (incM F (frame H')).map (cA σ)) * D.map (cA σ)) * (incM F (coframe hd H')).map (cA σ) := by
        simp only [Matrix.transpose_mul, hmap, Matrix.mul_assoc]
    _ = incM F W.J := by rw [hG, hD, ← hJ]

lemma dg_unitary (σ : E →ₐ[F] E) (J₁ : Matrix (Fin d₁) (Fin d₁) E) (a b : AE F E)
    (g : Matrix (Fin d₁) (Fin d₁) (AE F E)) (hg : gᵀ * incM F J₁ * g.map (cA σ) = incM F J₁)
    (hab : a * cA σ b = 1) (hba : b * cA σ a = 1) :
    (dg a b g)ᵀ * incM F (Matrix.fromBlocks J₁ 0 0 hyp) * (dg a b g).map (cA σ) =
      incM F (Matrix.fromBlocks J₁ 0 0 hyp) := by
  have e1 : incM F (Matrix.fromBlocks J₁ 0 0 hyp) = Matrix.fromBlocks (incM F J₁) 0 0 (incM F hyp) := by
    simp [incM, Matrix.fromBlocks_map]
  have e2 : (dg a b g).map (cA σ) = Matrix.fromBlocks (g.map (cA σ)) 0 0 (Matrix.diagonal ![cA σ a, cA σ b]) := by
    rw [dg, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _),
      Matrix.diagonal_map (map_zero _)]
    congr 2
    ext i; fin_cases i <;> rfl
  have hp : Matrix.diagonal ![a, b] * incM F hyp * Matrix.diagonal ![cA σ a, cA σ b] = incM F hyp := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j <;> simp [hyp, incM, hab, hba]
  rw [e1, e2, dg, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hg, hp]

theorem levi_unit_at : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ), B.IsGood σ →
    W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ v : Pl F,
    ∀ (t : (AE F E)ˣ) (h₁ : UA σ W₁.J), At (evFin F v) ((t : AE F E) - 1) → h₁ ∈ UAt σ W₁ (evFin F v) →
    ∃ m : UA σ W.J, IsLevi H' t h₁ m ∧ m ∈ UAt σ W (evFin F v) := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hA v t h₁ ht hh₁
  have hσ : ∀ z, σ (σ z) = z := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hu := isUnit_sq σ hσ B hW hW₁ hA
  have hinv : mat h₁ * mat h₁⁻¹ = 1 := by
    show ((h₁.1 * (h₁⁻¹).1 : GL (Fin d₁) (AE F E)) : Matrix (Fin d₁) (Fin d₁) (AE F E)) = 1
    rw [← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have hinv' : mat h₁⁻¹ * mat h₁ = 1 := by
    show (((h₁⁻¹).1 * h₁.1 : GL (Fin d₁) (AE F E)) : Matrix (Fin d₁) (Fin d₁) (AE F E)) = 1
    rw [← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have ht1 : (t : AE F E) * ((t⁻¹ : (AE F E)ˣ) : AE F E) = 1 := t.mul_inv
  have ht2 : ((t⁻¹ : (AE F E)ˣ) : AE F E) * t = 1 := t.inv_mul
  have hc1 : cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E) * cA σ (t : AE F E) = 1 := by rw [← map_mul, ht2, map_one]
  have hc2 : cA σ (t : AE F E) * cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by rw [← map_mul, ht1, map_one]
  let mU : GL (Fin d) (AE F E) :=
    ⟨mM hA.rank H' (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)) (mat h₁),
      mM hA.rank H' ((t⁻¹ : (AE F E)ˣ) : AE F E) (cA σ (t : AE F E)) (mat h₁⁻¹),
      by rw [mM_mul hu, ht1, hc1, hinv, mM_one hu], by rw [mM_mul hu, ht2, hc2, hinv', mM_one hu]⟩
  have hmem : mU ∈ UG (cA σ) (incM F W.J) :=
    conj_unitary σ hσ B hW hA hu _ (dg_unitary σ W₁.J _ _ _ h₁.2 (by rw [cA_cA σ hσ, ht1]) hc1)
  have hf := mM_frame (F := F) hu (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)) (mat h₁)
  rw [incM_frame, Matrix.mul_fromCols, dg, Matrix.fromCols_mul_fromBlocks] at hf
  simp only [Matrix.mul_zero, add_zero, zero_add] at hf
  obtain ⟨h1, h2⟩ := Matrix.fromCols_inj hf
  refine ⟨⟨mU, hmem⟩, ⟨?_, ?_, h1⟩, ?_⟩
  · funext i
    have := congrFun (congrFun h2 i) 0
    rw [Matrix.mul_diagonal] at this
    exact this.trans (mul_comm _ _)
  · funext i
    have := congrFun (congrFun h2 i) 1
    rw [Matrix.mul_diagonal] at this
    exact this.trans (mul_comm _ _)
  · intro u hu0
    show u • (mM hA.rank H' (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)) (mat h₁) - 1) = 0
    have hg : u • (mat h₁ - 1) = 0 := hh₁ u hu0
    have h0 : u • ((t : AE F E) - 1) = 0 := ht u hu0
    have h0' : u • (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E) - 1) = 0 := by
      have e : ((t⁻¹ : (AE F E)ˣ) : AE F E) - 1 = -((t⁻¹ : (AE F E)ˣ) : AE F E) * ((t : AE F E) - 1) := by
        linear_combination ht2
      rw [← map_one (cA σ), ← map_sub, ← map_smul, e, ← mul_smul_comm, h0, mul_zero, map_zero]
    have hz : u • (dg (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)) (mat h₁) - 1) = 0 := by
      ext (i|i) (j|j)
      · have := congrFun (congrFun hg i) j
        simpa [dg, Matrix.one_apply] using this
      · simp [dg, Matrix.one_apply]
      · simp [dg, Matrix.one_apply]
      · fin_cases i <;> fin_cases j <;> simp [dg, Matrix.one_apply, h0, h0']
    have hD : mM hA.rank H' (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)) (mat h₁) - 1 =
        incM F (frame H') * (dg (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)) (mat h₁) - 1) *
          incM F (coframe hA.rank H') := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, S_T hu]; rfl
    rw [hD, ← Matrix.smul_mul, ← Matrix.mul_smul, hz, Matrix.mul_zero, Matrix.zero_mul]

end GlobalTheory.PlaneLeviUnit
