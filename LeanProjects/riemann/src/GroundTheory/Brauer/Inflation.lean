import Mathlib
import GroundTheory.Brauer.CrossedProduct
import GroundTheory.Brauer.CrossedProductSimple
import GroundTheory.Brauer.CrossedProductMaps
import GroundTheory.Brauer.CrossedProductInj
import GroundTheory.Brauer.CrossedProductTensor
import GroundTheory.Brauer.IsBrauerEquivalentIffNonemptyAlgEquiv
import GroundTheory.Brauer.BaseChange
import GroundTheory.Brauer.MulDistribMulActionQuotientFixedPoints
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open groupCohomology

universe u

namespace CrossedProduct

section Inflate

variable {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [Normal K L]

theorem algebraMap_restrictNormalHom (σ : L' ≃ₐ[K] L') (x : L) :
    algebraMap L L' (AlgEquiv.restrictNormalHom L σ x) = σ (algebraMap L L' x) :=
  AlgEquiv.restrictNormal_commutes σ L x

theorem map_smul_restrictNormalHom (σ : L' ≃ₐ[K] L') (c : L) (y : L') :
    σ (c • y) = AlgEquiv.restrictNormalHom L σ c • σ y := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, algebraMap_restrictNormalHom]

theorem unitsMap_smul (σ : L' ≃ₐ[K] L') (m : Lˣ) :
    Units.map (algebraMap L L' : L →* L') (AlgEquiv.restrictNormalHom L σ • m) =
      σ • Units.map (algebraMap L L' : L →* L') m := by
  ext
  exact algebraMap_restrictNormalHom σ (m : L)

variable (L') in

def inflate (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) : (L' ≃ₐ[K] L') × (L' ≃ₐ[K] L') → L'ˣ :=
  fun p => Units.map (algebraMap L L' : L →* L')
    (f (AlgEquiv.restrictNormalHom L p.1, AlgEquiv.restrictNormalHom L p.2))

theorem val_inflate (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) (p : (L' ≃ₐ[K] L') × (L' ≃ₐ[K] L')) :
    ((inflate L' f p : L'ˣ) : L') =
      algebraMap L L' (f (AlgEquiv.restrictNormalHom L p.1, AlgEquiv.restrictNormalHom L p.2)) :=
  rfl

variable (L') in

theorem isMulCocycle₂_inflate {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f) :
    IsMulCocycle₂ (inflate L' f) :=
  (H2mul.mapCocycles₂ (AlgEquiv.restrictNormalHom L) (Units.map (algebraMap L L' : L →* L'))
    unitsMap_smul ⟨f, hf⟩).2

section Basis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι L L')

def galMatrix (σ : L' ≃ₐ[K] L') : Matrix ι ι L :=
  fun i j => b.repr (σ (b j)) i

omit [DecidableEq ι] in

theorem repr_apply_algEquiv (σ : L' ≃ₐ[K] L') (x : L') (i : ι) :
    b.repr (σ x) i = ∑ j, galMatrix b σ i j * AlgEquiv.restrictNormalHom L σ (b.repr x j) := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul_restrictNormalHom, map_smul, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, galMatrix]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

omit [DecidableEq ι] in

theorem galMatrix_mul (σ τ : L' ≃ₐ[K] L') :
    galMatrix b (σ * τ) = galMatrix b σ * (galMatrix b τ).map (AlgEquiv.restrictNormalHom L σ) := by
  ext i k
  change b.repr ((σ * τ) (b k)) i = _
  rw [AlgEquiv.mul_apply, repr_apply_algEquiv, Matrix.mul_apply]
  rfl

omit [Algebra K L] [IsScalarTower K L L'] [Normal K L] [Fintype ι] in

theorem galMatrix_one : galMatrix b (1 : L' ≃ₐ[K] L') = 1 := by
  ext i j
  simp only [galMatrix, AlgEquiv.one_apply, Module.Basis.repr_self, Finsupp.single_apply,
    Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

theorem galMatrix_mul_leftMulMatrix (σ : L' ≃ₐ[K] L') (a : L') :
    galMatrix b σ * (Algebra.leftMulMatrix b a).map (AlgEquiv.restrictNormalHom L σ) =
      Algebra.leftMulMatrix b (σ a) * galMatrix b σ := by
  ext i k
  have h : b.repr (σ (a * b k)) i =
      ∑ j, galMatrix b σ i j * AlgEquiv.restrictNormalHom L σ (Algebra.leftMulMatrix b a j k) := by
    rw [repr_apply_algEquiv]
    simp only [Algebra.leftMulMatrix_eq_repr_mul]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.map_apply]
  rw [← h, map_mul, ← Algebra.leftMulMatrix_mulVec_repr]
  rfl

end Basis

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι L L')
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f)

def inflateIncl : L' →ₐ[K] Matrix ι ι (CrossedProduct hf) :=
  (incl : L →ₐ[K] CrossedProduct hf).mapMatrix.comp ((Algebra.leftMulMatrix b).restrictScalars K)

def inflateU (σ : L' ≃ₐ[K] L') : Matrix ι ι (CrossedProduct hf) :=
  (galMatrix b σ).map incl * Matrix.diagonal fun _ => u (AlgEquiv.restrictNormalHom L σ)

omit [Normal K L] in
theorem inflateIncl_apply (a : L') :
    inflateIncl b hf a = (Algebra.leftMulMatrix b a).map incl :=
  rfl

omit [IsScalarTower K L L'] [Normal K L] in

theorem diagonal_u_mul_map_incl (τ : L ≃ₐ[K] L) (M : Matrix ι ι L) :
    (Matrix.diagonal fun _ => (u τ : CrossedProduct hf)) * M.map incl =
      (M.map τ).map incl * Matrix.diagonal fun _ => (u τ : CrossedProduct hf) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply, u_mul_incl]

omit [IsScalarTower K L L'] [Normal K L] in

theorem diagonal_u_mul_diagonal_u (σ τ : L ≃ₐ[K] L) :
    (Matrix.diagonal fun _ => (u σ : CrossedProduct hf)) * Matrix.diagonal (fun _ => u τ) =
      (algebraMap L (Matrix ι ι L) (f (σ, τ) : L)).map incl *
        Matrix.diagonal fun _ => (u (σ * τ) : CrossedProduct hf) := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext _
  simp only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  exact u_mul_u σ τ

theorem inflateU_mul_inflateIncl (σ : L' ≃ₐ[K] L') (a : L') :
    inflateU b hf σ * inflateIncl b hf a = inflateIncl b hf (σ a) * inflateU b hf σ := by
  rw [inflateU, inflateIncl_apply, inflateIncl_apply, mul_assoc, diagonal_u_mul_map_incl,
    ← mul_assoc, ← Matrix.map_mul, galMatrix_mul_leftMulMatrix, Matrix.map_mul, mul_assoc]

theorem inflateU_mul_inflateU (σ τ : L' ≃ₐ[K] L') :
    inflateU b hf σ * inflateU b hf τ =
      inflateIncl b hf (inflate L' f (σ, τ) : L') * inflateU b hf (σ * τ) := by
  rw [inflateU, inflateU, inflateU, inflateIncl_apply, val_inflate, mul_assoc,
    ← mul_assoc (Matrix.diagonal _), diagonal_u_mul_map_incl, mul_assoc,
    diagonal_u_mul_diagonal_u, ← mul_assoc, ← mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul,
    ← galMatrix_mul, ← map_mul, AlgHom.commutes, ← mul_assoc, ← Matrix.map_mul,
    Algebra.commutes]

theorem inflateU_one :
    inflateU b hf 1 = inflateIncl b hf (inflate L' f (1, 1) : L') := by
  rw [inflateU, inflateIncl_apply, val_inflate, map_one, galMatrix_one, AlgHom.commutes,
    Matrix.map_one _ (map_zero _) (map_one _), one_mul, u_one, Matrix.algebraMap_eq_diagonal,
    Matrix.diagonal_map (map_zero _)]
  rfl

def inflateHom :
    CrossedProduct (isMulCocycle₂_inflate L' hf) →ₐ[K] Matrix ι ι (CrossedProduct hf) :=
  lift (inflateIncl b hf) (inflateU b hf) (inflateU_mul_inflateIncl b hf)
    (inflateU_mul_inflateU b hf) (inflateU_one b hf)

variable [FiniteDimensional K L] [IsGalois K L] [FiniteDimensional K L'] [IsGalois K L']
  [Nonempty ι]

theorem inflateHom_bijective : Function.Bijective (inflateHom b hf) := by
  have hinj : Function.Injective (inflateHom b hf) :=
    RingHom.injective (inflateHom b hf).toRingHom
  refine ⟨hinj, ?_⟩
  have hdim : Module.finrank K (CrossedProduct (isMulCocycle₂_inflate L' hf)) =
      Module.finrank K (Matrix ι ι (CrossedProduct hf)) := by
    rw [finrank_eq_sq, Module.finrank_matrix, finrank_eq_sq, ← Module.finrank_eq_card_basis b,
      ← Module.finrank_mul_finrank K L L']
    ring
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (inflateHom b hf).toLinearMap)).1 hinj

def inflateAlgEquiv :
    CrossedProduct (isMulCocycle₂_inflate L' hf) ≃ₐ[K] Matrix ι ι (CrossedProduct hf) :=
  AlgEquiv.ofBijective _ (inflateHom_bijective b hf)

end Matrix

end Inflate

section Brauer

variable {K L L' : Type u} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [FiniteDimensional K L] [IsGalois K L]
  [FiniteDimensional K L'] [IsGalois K L']

variable (L') in

theorem isBrauerEquivalent_inflate {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f) :
    IsBrauerEquivalent (csaOf K (CrossedProduct (isMulCocycle₂_inflate L' hf)))
      (csaOf K (CrossedProduct hf)) := by
  have : FiniteDimensional L L' := Module.Finite.of_restrictScalars_finite K L L'
  have : Nonempty (Fin (Module.finrank L L')) := ⟨⟨0, Module.finrank_pos⟩⟩
  exact isBrauerEquivalent_of_algEquiv_matrix (C := CrossedProduct hf)
    (inflateAlgEquiv (Module.finBasis L L') hf) (matrixFinOneAlgEquiv (CrossedProduct hf)).symm

end Brauer

end CrossedProduct

namespace BrauerGroup

variable (K L L' : Type u) [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L']

theorem relBrauer_le_relBrauer : relBrauer K L ≤ relBrauer K L' := by
  intro x hx
  rw [mem_relBrauer_iff] at hx ⊢
  rw [← baseChange_baseChange K L L', hx, map_one]

end BrauerGroup

namespace H2mul

section Inflation

variable (K L L' : Type*) [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [Normal K L]

def inflation : H2mul (L ≃ₐ[K] L) Lˣ →* H2mul (L' ≃ₐ[K] L') L'ˣ :=
  mapPair (AlgEquiv.restrictNormalHom L) (Units.map (algebraMap L L' : L →* L'))
    CrossedProduct.unitsMap_smul

variable {K L L'}

theorem inflation_mk (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) :
    inflation K L L' (mk _ _ c) =
      mk _ _ ⟨CrossedProduct.inflate L' (c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ),
        CrossedProduct.isMulCocycle₂_inflate L' c.2⟩ :=
  rfl

end Inflation

section Brauer

variable {K L L' : Type u} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [FiniteDimensional K L] [IsGalois K L]
  [FiniteDimensional K L'] [IsGalois K L']

theorem toBrauer_inflation (x : H2mul (L ≃ₐ[K] L) Lˣ) :
    toBrauer K L' (inflation K L L' x) = toBrauer K L x := by
  induction x using H2mul.induction_on with
  | h c =>
  rw [inflation_mk, toBrauer_mk, toBrauer_mk]
  exact Quotient.sound (CrossedProduct.isBrauerEquivalent_inflate L' c.2)

theorem inflation_injective : Function.Injective (inflation K L L') := by
  intro x y h
  apply toBrauer_injective (K := K) (L := L)
  have h' := congrArg (toBrauer K L') h
  rwa [toBrauer_inflation, toBrauer_inflation] at h'

end Brauer

end H2mul

end GroundTheory.Brauer

end
