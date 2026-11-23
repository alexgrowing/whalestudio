import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.IsFibreFamilyReindex

noncomputable section

namespace PI.DegenerateSiegelWeil.Scale

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolStabSW
open scoped ENNReal NNReal TensorProduct Matrix

section Alg

variable {K : Type} [CommRing K] {n M : ℕ}

def mulTup (D : Matrix (Fin n) (Fin n) K) (X : Fin n → Fin M → K) : Fin n → Fin M → K :=
  fun j i => ∑ k, D k j * X k i

theorem mulTup_mul (D₁ D₂ : Matrix (Fin n) (Fin n) K) (X : Fin n → Fin M → K) :
    mulTup D₁ (mulTup D₂ X) = mulTup (D₂ * D₁) X := by
  funext j i
  simp only [mulTup, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem mulTup_one (X : Fin n → Fin M → K) : mulTup (1 : Matrix (Fin n) (Fin n) K) X = X := by
  funext j i
  simp [mulTup, Matrix.one_apply]

theorem mulTup_add (D : Matrix (Fin n) (Fin n) K) (X Y : Fin n → Fin M → K) :
    mulTup D (X + Y) = mulTup D X + mulTup D Y := by
  funext j i
  simp [mulTup, mul_add, Finset.sum_add_distrib]

theorem mulTup_apply_eq_sum (D : Matrix (Fin n) (Fin n) K) (X : Fin n → Fin M → K) (j : Fin n) :
    mulTup D X j = ∑ k, D k j • X k := by
  funext i
  simp [mulTup, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem linIndep_mulTup (D : (Matrix (Fin n) (Fin n) K)ˣ) {X : Fin n → Fin M → K}
    (hX : LinearIndependent K X) : LinearIndependent K (mulTup (D : Matrix (Fin n) (Fin n) K) X) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro c hc
  have key : ∑ j, c j • mulTup (D : Matrix (Fin n) (Fin n) K) X j =
      ∑ k, Matrix.mulVec (D : Matrix (Fin n) (Fin n) K) c k • X k := by
    simp only [mulTup_apply_eq_sum, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct,
      Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  have h0 : Matrix.mulVec (D : Matrix (Fin n) (Fin n) K) c = 0 := funext (hX _ (key ▸ hc))
  have hc0 : c = 0 := by
    have h1 := congrArg (Matrix.mulVec ((D⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K)) h0
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
  intro j
  rw [hc0]
  rfl

theorem preimage_linIndep (D : (Matrix (Fin n) (Fin n) K)ˣ) :
    mulTup (M := M) (D : Matrix (Fin n) (Fin n) K) ⁻¹' {X | LinearIndependent K X} =
      {X | LinearIndependent K X} := by
  ext X
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · intro h
    have h1 := linIndep_mulTup D⁻¹ h
    rwa [mulTup_mul, Units.mul_inv, mulTup_one] at h1
  · exact linIndep_mulTup D

end Alg

section Herm

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n M : ℕ}

def conjT (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (D.map (sigR R σ))ᵀ

theorem conjT_mul (A B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    conjT R σ (A * B) = conjT R σ B * conjT R σ A := by
  unfold conjT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem conjT_one : conjT R σ (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1 := by
  simp [conjT]

theorem sigR_sigR (hσ : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) : sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, Algebra.TensorProduct.map_tmul, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem conjT_conjT (hσ : ∀ x, σ (σ x) = x) (A : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    conjT R σ (conjT R σ A) = A := by
  ext i j
  simp [conjT, sigR_sigR R σ hσ]

theorem mem_herm_iff (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    S ∈ HermR R σ n ↔ conjT R σ S = S := by
  constructor
  · intro h
    have h' : ∀ a b, sigR R σ ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) b a) = S a b := h
    ext a b
    exact h' a b
  · intro h
    have h' : ∀ a b, sigR R σ ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) b a) = S a b := by
      intro a b
      have := congrFun (congrFun h a) b
      simpa [conjT] using this
    exact h'

def hermMap (hσ : ∀ x, σ (σ x) = x) (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (S : HermR R σ n) :
    HermR R σ n :=
  ⟨conjT R σ D * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * D, by
    rw [mem_herm_iff, conjT_mul, conjT_mul, conjT_conjT R σ hσ, (mem_herm_iff R σ _).1 S.2,
      Matrix.mul_assoc]⟩

theorem hermMap_coe (hσ : ∀ x, σ (σ x) = x) (D : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (S : HermR R σ n) :
    (hermMap R σ hσ D S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = conjT R σ D * S * D := rfl

theorem hermMap_mul (hσ : ∀ x, σ (σ x) = x) (D₁ D₂ : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (S : HermR R σ n) : hermMap R σ hσ D₁ (hermMap R σ hσ D₂ S) = hermMap R σ hσ (D₂ * D₁) S := by
  apply Subtype.ext
  simp only [hermMap_coe, conjT_mul, Matrix.mul_assoc]

theorem hermMap_one (hσ : ∀ x, σ (σ x) = x) (S : HermR R σ n) : hermMap R σ hσ 1 S = S := by
  apply Subtype.ext
  simp [hermMap_coe, conjT_one]

def tupS (X : Fin n → Fin M → R ⊗[F] E) : Matrix (Fin n) (Fin M) (R ⊗[F] E) :=
  Matrix.of fun a i => sigR R σ (X a i)

def tupT (X : Fin n → Fin M → R ⊗[F] E) : Matrix (Fin M) (Fin n) (R ⊗[F] E) :=
  Matrix.of fun i b => X b i

def jM (J : Matrix (Fin M) (Fin M) E) : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  Matrix.of fun i j => inclR R (J i j)

end Herm

def GramMulTup : Prop := ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
  [Algebra F R] (σ : E →ₐ[F] E) (n M : ℕ) (J : Matrix (Fin M) (Fin M) E)
  (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E),
  gramR R σ J (mulTup D X) = conjT R σ D * gramR R σ J X * D

theorem gramH_mulTup_of (hG : GramMulTup) {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) :
    PI.VolStabSW.gramH R σ hσ J hJ (mulTup D X) =
      hermMap R σ hσ D (PI.VolStabSW.gramH R σ hσ J hJ X) := by
  apply Subtype.ext
  rw [hermMap_coe]
  exact hG F E R σ n M J D X

end PI.DegenerateSiegelWeil.Scale
