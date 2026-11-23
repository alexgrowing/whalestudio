import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.SiegelConv

def ratP {F : Type} [Field F] [NumberField F] {κ : Type} (w : (κ → F) × (κ → F)) : (κ → AF F) × (κ → AF F) :=
  (fun i => algebraMap F (AF F) (w.1 i), fun i => algebraMap F (AF F) (w.2 i))

def extA {F : Type} [Field F] [NumberField F] {m κ : Type} [Fintype m] [DecidableEq m]
    (A : (m → F) →ₗ[F] (κ → F) × (κ → F)) (t : m → AF F) : (κ → AF F) × (κ → AF F) :=
  ∑ j, t j • ratP (A (Pi.single j 1))

def vecOf (F : Type) [Field F] {E : Type} [Field E] [Algebra F E] [Module.Finite F E] {n : ℕ}
    (s : Fin n × Fin (Module.finrank F E) → F) : Fin n → E :=
  fun j => ∑ i, s (j, i) • Module.finBasis F E i

def basisMap (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (t : Fin n × Fin (Module.finrank F E) → AF F) : Fin n → AE F E :=
  fun j => ∑ i, t (j, i) • inclR (F := F) (AF F) (Module.finBasis F E i)

def lagP {E : Type} [Field E] (n : ℕ) {d d₁ : ℕ} (ι : Matrix (Fin d) (Fin d₁) E) (x : Fin d → E) :
    Matrix (Fin d₁) (Fin n) E × (Fin n ⊕ Fin n → E) →ₗ[E] Matrix (Fin d) (Fin n ⊕ Fin n) E where
  toFun p := ι * (p.1 * Matrix.transpose (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E)) + Matrix.vecMulVec x p.2
  map_add' p q := by
    have h : Matrix.vecMulVec x (p.2 + q.2) = Matrix.vecMulVec x p.2 + Matrix.vecMulVec x q.2 := by
      ext i j; simp [Matrix.vecMulVec_apply, mul_add]
    simp only [Prod.fst_add, Prod.snd_add, Matrix.add_mul, Matrix.mul_add, h]
    abel
  map_smul' c p := by
    have h : Matrix.vecMulVec x (c • p.2) = c • Matrix.vecMulVec x p.2 := by
      ext i j; simp [Matrix.vecMulVec_apply, mul_left_comm]
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, Matrix.smul_mul, Matrix.mul_smul, smul_add, h]

def vvMap (F : Type) [Field F] {E : Type} [Field E] [Algebra F E] [Module.Finite F E] {n d : ℕ} (w : Fin d → E) :
    (Fin n × Fin (Module.finrank F E) → F) →ₗ[F] Matrix (Fin d) (Fin n ⊕ Fin n) E where
  toFun s := Matrix.vecMulVec w (Sum.elim (vecOf F s) (vecOf F s))
  map_add' s s' := by
    ext i j
    rcases j with j | j <;>
      simp [Matrix.vecMulVec_apply, vecOf, add_smul, Finset.sum_add_distrib, mul_add]
  map_smul' c s := by
    ext i j
    rcases j with j | j <;>
    · simp only [Matrix.vecMulVec_apply, vecOf, Pi.smul_apply, smul_eq_mul, Sum.elim_inl, Sum.elim_inr,
        Matrix.smul_apply, RingHom.id_apply, Finset.mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_smul, mul_smul_comm]

theorem ratDot {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (u v : κ → F) :
    (fun i => algebraMap F (AF F) (u i)) ⬝ᵥ (fun i => algebraMap F (AF F) (v i)) = algebraMap F (AF F) (u ⬝ᵥ v) :=
  (RingHom.map_dotProduct (algebraMap F (AF F)) u v).symm

theorem map_diagCols {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E).map (inclR (F := F) (AF F)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) := by
  rw [diagCols, diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero _) (map_one _)]

theorem smul_incM_lagP {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d d₁ : ℕ}
    (ι : Matrix (Fin d) (Fin d₁) E) (x : Fin d → E) (t : AF F) (p : Matrix (Fin d₁) (Fin n) E × (Fin n ⊕ Fin n → E)) :
    t • incM F (lagP n ι x p) = incM F ι * ((t • incM F p.1) * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) +
      Matrix.vecMulVec (incV F x) (fun i => t • inclR (F := F) (AF F) (p.2 i)) := by
  have hΔ : ∀ a b, inclR (F := F) (AF F) ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) a b) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) a b := fun a b => by
    rw [← map_diagCols (F := F) n]; rfl
  ext i j
  simp only [lagP, LinearMap.coe_mk, AddHom.coe_mk, incM, Matrix.smul_apply, Matrix.map_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.vecMulVec_apply, incV, map_add, map_sum, map_mul, Matrix.transpose_apply, smul_add,
    Finset.smul_sum, hΔ, smul_eq_mul]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_smul_comm, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_mul_assoc]
  · rw [mul_smul_comm]

end GlobalTheory.SiegelConv

end
