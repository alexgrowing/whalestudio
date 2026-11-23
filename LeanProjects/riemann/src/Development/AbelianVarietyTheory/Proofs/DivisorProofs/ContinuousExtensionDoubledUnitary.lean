import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeviElement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DblLeviExt

open GlobalTheory.PlaneLeviExt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {d d₁ : ℕ}

def perm (d₁ : ℕ) : (Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2) ≃ (Fin d₁ ⊕ Fin d₁) ⊕ (Fin 2 ⊕ Fin 2) :=
  Equiv.sumSumSumComm _ _ _ _

variable (F) in

def DS (H' : Plane E d d₁) : Matrix (Fin d ⊕ Fin d) ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) (AE F E) :=
  Matrix.fromBlocks (incM F (frame H')) 0 0 (incM F (frame H'))

variable (F) in

def DT (hd : d = d₁ + 2) (H' : Plane E d d₁) : Matrix ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) (Fin d ⊕ Fin d) (AE F E) :=
  Matrix.fromBlocks (incM F (coframe hd H')) 0 0 (incM F (coframe hd H'))

variable (F) in

def dP (H' : Plane E d d₁) : Matrix (Fin d ⊕ Fin d) ((Fin d₁ ⊕ Fin d₁) ⊕ (Fin 2 ⊕ Fin 2)) (AE F E) :=
  (DS F H').submatrix id (perm d₁).symm

variable (F) in

def dPinv (hd : d = d₁ + 2) (H' : Plane E d d₁) : Matrix ((Fin d₁ ⊕ Fin d₁) ⊕ (Fin 2 ⊕ Fin 2)) (Fin d ⊕ Fin d) (AE F E) :=
  (DT F hd H').submatrix (perm d₁).symm id

def blk2 (g : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) :
    Matrix ((Fin d₁ ⊕ Fin d₁) ⊕ (Fin 2 ⊕ Fin 2)) ((Fin d₁ ⊕ Fin d₁) ⊕ (Fin 2 ⊕ Fin 2)) (AE F E) :=
  Matrix.fromBlocks g 0 0 1

def extM (hd : d = d₁ + 2) (H' : Plane E d d₁) (g : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
  dP F H' * blk2 g * dPinv F hd H'

variable {hd : d = d₁ + 2} {H' : Plane E d d₁}

lemma DS_DT (hu : IsUnit (sq hd H')) : DS F H' * DT F hd H' = 1 := by
  simp [DS, DT, Matrix.fromBlocks_multiply, S_T hu]

lemma DT_DS (hu : IsUnit (sq hd H')) : DT F hd H' * DS F H' = 1 := by
  simp [DS, DT, Matrix.fromBlocks_multiply, T_S hu]

lemma P_Pinv (hu : IsUnit (sq hd H')) : dP F H' * dPinv F hd H' = 1 := by
  rw [dP, dPinv, Matrix.submatrix_mul_equiv, DS_DT hu, Matrix.submatrix_id_id]

lemma Pinv_P (hu : IsUnit (sq hd H')) : dPinv F hd H' * dP F H' = 1 := by
  have : dPinv F hd H' * dP F H' = (DT F hd H' * DS F H').submatrix (perm d₁).symm (perm d₁).symm :=
    Matrix.submatrix_mul_equiv (DT F hd H') (DS F H') (perm d₁).symm (Equiv.refl _) (perm d₁).symm
  rw [this, DT_DS hu, Matrix.submatrix_one_equiv]

lemma extM_mul (hu : IsUnit (sq hd H')) (g g' : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) :
    extM hd H' g * extM hd H' g' = extM hd H' (g * g') := by
  simp only [extM, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dPinv F hd H'), Pinv_P hu, Matrix.one_mul, ← Matrix.mul_assoc (blk2 g), blk2, blk2, blk2,
    Matrix.fromBlocks_multiply]
  simp

lemma extM_one (hu : IsUnit (sq hd H')) : extM (F := F) hd H' 1 = 1 := by
  rw [extM, blk2, Matrix.fromBlocks_one, Matrix.mul_one, P_Pinv hu]

end GlobalTheory.DblLeviExt

namespace GlobalTheory.DblLeviExt
open GlobalTheory.PlaneLeviExt
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {d d₁ : ℕ} {hd : d = d₁ + 2} {H' : Plane E d d₁}

lemma gram_DS (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {W : Spc F E d}
    {W₁ : Spc F E d₁} {i₀ i₁ r' s' : ℕ} (hW : W.IsSkew σ B r' s') (hA : H'.IsAdapted σ B W W₁ i₀ i₁) :
    (DS F H')ᵀ * dbl (incM F W.J) * (DS F H').map (cA σ) = dbl (incM F (Matrix.fromBlocks W₁.J 0 0 hyp)) := by
  have hG : (incM F (frame H'))ᵀ * incM F W.J * (incM F (frame H')).map (cA σ) =
      incM F (Matrix.fromBlocks W₁.J 0 0 hyp) := by
    rw [← gram_frame σ hσ B hW hA, incM_mul, incM_mul, incM_transpose, cA_incM]
  rw [DS, dbl, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp [hG]

lemma gram_P (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {W : Spc F E d}
    {W₁ : Spc F E d₁} {i₀ i₁ r' s' : ℕ} (hW : W.IsSkew σ B r' s') (hA : H'.IsAdapted σ B W W₁ i₀ i₁) :
    (dP F H')ᵀ * dbl (incM F W.J) * (dP F H').map (cA σ) =
      Matrix.fromBlocks (dbl (incM F W₁.J)) 0 0 (dbl (incM F hyp)) := by
  have h1 : (dP F H')ᵀ * dbl (incM F W.J) * (dP F H').map (cA σ) =
      ((DS F H')ᵀ * dbl (incM F W.J) * (DS F H').map (cA σ)).submatrix (perm d₁).symm (perm d₁).symm := rfl
  rw [h1, gram_DS σ hσ B hW hA]
  ext ((i | i) | (i | i)) ((j | j) | (j | j)) <;> simp [dbl, perm, incM, Matrix.fromBlocks_map]

end GlobalTheory.DblLeviExt

namespace GlobalTheory.DblLeviExt
open GlobalTheory.PlaneLeviExt
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {d d₁ : ℕ} {hd : d = d₁ + 2} {H' : Plane E d d₁}

lemma extM_unitary (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {W : Spc F E d}
    {W₁ : Spc F E d₁} {i₀ i₁ r' s' : ℕ} (hW : W.IsSkew σ B r' s') (hA : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hu : IsUnit (sq hd H')) (g : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E))
    (hg : gᵀ * dbl (incM F W₁.J) * g.map (cA σ) = dbl (incM F W₁.J)) :
    (extM hd H' g)ᵀ * dbl (incM F W.J) * (extM hd H' g).map (cA σ) = dbl (incM F W.J) := by
  have hmap : ∀ {a b c : Type} [Fintype b] (X : Matrix a b (AE F E)) (Y : Matrix b c (AE F E)),
      (X * Y).map (cA σ) = X.map (cA σ) * Y.map (cA σ) := fun X Y => Matrix.map_mul (f := (cA σ).toRingHom)
  have hG := gram_P σ hσ B hW hA
  have hJ : dbl (incM F W.J) = (dPinv F hd H')ᵀ * ((dP F H')ᵀ * dbl (incM F W.J) * (dP F H').map (cA σ)) *
      (dPinv F hd H').map (cA σ) := by
    have h1 : (dP F H' * dPinv F hd H')ᵀ * dbl (incM F W.J) * (dP F H' * dPinv F hd H').map (cA σ) =
        dbl (incM F W.J) := by
      rw [P_Pinv hu, Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
    conv_lhs => rw [← h1]
    rw [Matrix.transpose_mul, hmap]; simp only [Matrix.mul_assoc]
  have hB : (blk2 g)ᵀ * Matrix.fromBlocks (dbl (incM F W₁.J)) 0 0 (dbl (incM F hyp)) * (blk2 g).map (cA σ) =
      Matrix.fromBlocks (dbl (incM F W₁.J)) 0 0 (dbl (incM F hyp)) := by
    have e2 : (blk2 g).map (cA σ) = Matrix.fromBlocks (g.map (cA σ)) 0 0 1 := by
      rw [blk2, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _),
        Matrix.map_one _ (map_zero _) (map_one _)]
    rw [e2, blk2, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [hg]
  calc (extM hd H' g)ᵀ * dbl (incM F W.J) * (extM hd H' g).map (cA σ)
      = (dPinv F hd H')ᵀ * ((blk2 g)ᵀ * ((dP F H')ᵀ * dbl (incM F W.J) *
          (dP F H').map (cA σ)) * (blk2 g).map (cA σ)) * (dPinv F hd H').map (cA σ) := by
        simp only [extM, Matrix.transpose_mul, hmap, Matrix.mul_assoc]
    _ = dbl (incM F W.J) := by rw [hG, hB, ← hG, ← hJ]

def cX (H' : Plane E d d₁) : Matrix (Fin d ⊕ Fin d) (Fin d₁ ⊕ Fin d₁) (AE F E) :=
  Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι)

def cQ (H' : Plane E d d₁) : Matrix (Fin d ⊕ Fin d) (Fin 2 ⊕ Fin 2) (AE F E) :=
  Matrix.fromBlocks (incM F (twoCols H')) 0 0 (incM F (twoCols H'))

lemma dP_eq : dP F H' = Matrix.fromCols (cX (F := F) H') (cQ H') := by
  ext (i | i) ((j | j) | (j | j)) <;> simp [dP, DS, perm, cX, cQ, incM_frame]

lemma mul_cQ_iff (m : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) :
    m * cQ (F := F) H' = cQ H' ↔
      m *ᵥ Sum.elim (incV F H'.x) (0 : Fin d → AE F E) = Sum.elim (incV F H'.x) (0 : Fin d → AE F E) ∧
      m *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.x) = Sum.elim (0 : Fin d → AE F E) (incV F H'.x) ∧
      m *ᵥ Sum.elim (incV F H'.y) (0 : Fin d → AE F E) = Sum.elim (incV F H'.y) (0 : Fin d → AE F E) ∧
      m *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.y) = Sum.elim (0 : Fin d → AE F E) (incV F H'.y) := by
  have hcol : m * cQ (F := F) H' = cQ H' ↔ ∀ c, m *ᵥ (fun i => cQ (F := F) H' i c) = fun i => cQ (F := F) H' i c := by
    constructor
    · intro h c; funext i; exact congrFun (congrFun h i) c
    · intro h; ext i c; exact congrFun (h c) i
  have c1 : (fun i => cQ (F := F) H' i (Sum.inl 0)) = Sum.elim (incV F H'.x) (0 : Fin d → AE F E) := by
    funext i; rcases i with i | i <;> simp [cQ, incM, incV, twoCols]
  have c2 : (fun i => cQ (F := F) H' i (Sum.inl 1)) = Sum.elim (incV F H'.y) (0 : Fin d → AE F E) := by
    funext i; rcases i with i | i <;> simp [cQ, incM, incV, twoCols]
  have c3 : (fun i => cQ (F := F) H' i (Sum.inr 0)) = Sum.elim (0 : Fin d → AE F E) (incV F H'.x) := by
    funext i; rcases i with i | i <;> simp [cQ, incM, incV, twoCols]
  have c4 : (fun i => cQ (F := F) H' i (Sum.inr 1)) = Sum.elim (0 : Fin d → AE F E) (incV F H'.y) := by
    funext i; rcases i with i | i <;> simp [cQ, incM, incV, twoCols]
  rw [hcol, Sum.forall, Fin.forall_fin_two, Fin.forall_fin_two, c1, c2, c3, c4]
  tauto

lemma cols_iff (m : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) (g : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) :
    m * dP F H' = dP F H' * blk2 g ↔ m * cX (F := F) H' = cX H' * g ∧ m * cQ (F := F) H' = cQ H' := by
  rw [dP_eq, Matrix.mul_fromCols, blk2, Matrix.fromCols_mul_fromBlocks]
  simp only [Matrix.mul_zero, add_zero, Matrix.mul_one, zero_add]
  rw [Matrix.fromCols_inj.eq_iff]
  exact Iff.rfl

end GlobalTheory.DblLeviExt

namespace GlobalTheory.DblLeviExt
open GlobalTheory.PlaneLeviExt
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {d d₁ : ℕ} {H' : Plane E d d₁}

def extU (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {W : Spc F E d} {W₁ : Spc F E d₁}
    {i₀ i₁ r' s' r₁ s₁ : ℕ} (hW : W.IsSkew σ B r' s') (hW₁ : W₁.IsSkew σ B r₁ s₁) (hA : H'.IsAdapted σ B W W₁ i₀ i₁)
    (g₁ : UG (cA σ) (dbl (incM F W₁.J))) : UG (cA σ) (dbl (incM F W.J)) :=
  ⟨⟨extM hA.rank H' g₁.1.1, extM hA.rank H' (↑(g₁.1⁻¹)),
    by rw [extM_mul (isUnit_sq σ hσ B hW hW₁ hA), Units.mul_inv, extM_one (isUnit_sq σ hσ B hW hW₁ hA)],
    by rw [extM_mul (isUnit_sq σ hσ B hW hW₁ hA), Units.inv_mul, extM_one (isUnit_sq σ hσ B hW hW₁ hA)]⟩,
   extM_unitary σ hσ B hW hA (isUnit_sq σ hσ B hW hW₁ hA) _ g₁.2⟩

theorem dbl_ext_existsUnique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r' s' r₁ s₁ : ℕ),
    W.IsSkew σ B r' s' → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∃ ext : UG (cA σ) (dbl (incM F W₁.J)) → UG (cA σ) (dbl (incM F W.J)), Continuous ext ∧
      ∀ (g₁ : UG (cA σ) (dbl (incM F W₁.J))) (g : UG (cA σ) (dbl (incM F W.J))),
        ((g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι) =
          Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι) * (g₁.1.1 : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (incV F H'.x) (0 : Fin d → AE F E) = Sum.elim (incV F H'.x) (0 : Fin d → AE F E) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.x) = Sum.elim (0 : Fin d → AE F E) (incV F H'.x) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (incV F H'.y) (0 : Fin d → AE F E) = Sum.elim (incV F H'.y) (0 : Fin d → AE F E) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.y) = Sum.elim (0 : Fin d → AE F E) (incV F H'.y)) ↔ g = ext g₁ := by
  intro F E _ _ _ _ _ σ B hB d d₁ W W₁ H' i₀ i₁ r' s' r₁ s₁ hW hW₁ hA
  have hσ : ∀ z, σ (σ z) = z := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hu := isUnit_sq σ hσ B hW hW₁ hA
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  refine ⟨extU σ hσ B hW hW₁ hA, ?_, fun g₁ g => ?_⟩
  · have hv : Continuous fun g₁ : UG (cA σ) (dbl (incM F W₁.J)) => (g₁.1.1 : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) :=
      Units.continuous_val.comp continuous_subtype_val
    have hi : Continuous fun g₁ : UG (cA σ) (dbl (incM F W₁.J)) =>
        ((g₁.1⁻¹ : GL (Fin d₁ ⊕ Fin d₁) (AE F E)) : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) :=
      Units.continuous_coe_inv.comp continuous_subtype_val
    have hc : ∀ f : UG (cA σ) (dbl (incM F W₁.J)) → Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E),
        Continuous f → Continuous fun g₁ => extM hA.rank H' (f g₁) := by
      intro f hf
      simp only [extM, blk2]
      exact (continuous_const.matrix_mul (Continuous.matrix_fromBlocks hf continuous_const continuous_const
        continuous_const)).matrix_mul continuous_const
    refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hc _ hv, hc _ hi⟩)
  · have key : (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * dP F H' = dP F H' * blk2 g₁.1.1 ↔
        g = extU σ hσ B hW hW₁ hA g₁ := by
      constructor
      · intro h
        apply Subtype.ext; apply Units.ext
        show (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) = extM hA.rank H' g₁.1.1
        calc (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))
            = g.1.1 * (dP F H' * dPinv F hA.rank H') := by rw [P_Pinv hu, Matrix.mul_one]
          _ = extM hA.rank H' g₁.1.1 := by rw [← Matrix.mul_assoc, h]; rfl
      · rintro rfl
        show extM hA.rank H' g₁.1.1 * dP F H' = _
        rw [extM, Matrix.mul_assoc, Pinv_P hu, Matrix.mul_one]
    rw [← key, cols_iff, mul_cQ_iff]
    rfl

end GlobalTheory.DblLeviExt
