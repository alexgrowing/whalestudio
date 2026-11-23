import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedHermN
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary

noncomputable section

open scoped Matrix NNReal TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling

namespace GlobalTheory.LocIntw

section Blocks

variable {A B : Type} [CommRing A] [CommRing B] {n : ℕ}

theorem blockMatrix_map (f : A →+* B) (a b c d : Matrix (Fin n) (Fin n) A) :
    (StdUnn.blk4 a b c d).map f = StdUnn.blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  ext i j
  simp only [StdUnn.blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem cT_blk4 (τ : A →+* A) (a b c d : Matrix (Fin n) (Fin n) A) :
    cT τ (StdUnn.blk4 a b c d) = StdUnn.blk4 (cT τ a) (cT τ c) (cT τ b) (cT τ d) := by
  ext i j
  simp only [cT, StdUnn.blk4, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem cT_zero' (τ : A →+* A) : cT τ (0 : Matrix (Fin n) (Fin n) A) = 0 := by
  ext i j; simp [cT]

theorem cT_one' (τ : A →+* A) : cT τ (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  ext i j; by_cases h : i = j <;> simp [cT, Matrix.one_apply, h, eq_comm]

theorem cT_neg_one (τ : A →+* A) : cT τ (-1 : Matrix (Fin n) (Fin n) A) = -1 := by
  ext i j; by_cases h : i = j <;> simp [cT, Matrix.one_apply, h, eq_comm]

theorem upperLeft_blockMatrix (a b c d : Matrix (Fin n) (Fin n) A) : StdUnn.blkA (StdUnn.blk4 a b c d) = a := by
  simp [StdUnn.blkA, StdUnn.blk4, Matrix.submatrix_submatrix, Matrix.toBlocks_fromBlocks₁₁]

theorem blockMatrix_mulVec_lower (a b c d : Matrix (Fin n) (Fin n) A) (x : Fin (n + n) → A) (i : Fin n) :
    (StdUnn.blk4 a b c d *ᵥ x) (finSumFinEquiv (Sum.inr i)) =
      (c *ᵥ fun j => x (finSumFinEquiv (Sum.inl j))) i + (d *ᵥ fun j => x (finSumFinEquiv (Sum.inr j))) i := by
  simp only [Matrix.mulVec, dotProduct, StdUnn.blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

end Blocks

section Points

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

def matR (g : HA R σ Q) : Matrix (Fin (n + n)) (Fin (n + n)) (R ⊗[F] E) := (matHom R σ Q g).1

variable {R σ} in

theorem ext_matR {g h : HA R σ Q} (e : matR R σ g = matR R σ h) : g = h :=
  matHom_injective R σ Q (Units.ext e)

theorem matR_mul (g h : HA R σ Q) : matR R σ (g * h) = matR R σ g * matR R σ h := rfl

theorem matR_one : matR R σ (1 : HA R σ Q) = 1 := rfl

theorem JR_eq (hQ : Q = StdUnn.blk4 0 1 (-1) 0) : JR (F := F) R Q = StdUnn.blk4 0 1 (-1) 0 := by
  subst hQ
  rw [JR, blockMatrix_map]
  congr 1
  · exact Matrix.map_zero _ (map_zero _)
  · exact Matrix.map_one _ (map_zero _) (map_one _)
  · rw [Matrix.map_neg _ (map_neg _), Matrix.map_one _ (map_zero _) (map_one _)]
  · exact Matrix.map_zero _ (map_zero _)

def mkPt (M N : Matrix (Fin (n + n)) (Fin (n + n)) (R ⊗[F] E)) (h1 : M * N = 1) (h2 : N * M = 1)
    (h : cT (sigR R σ) M * JR R Q * M = JR R Q) : HA R σ Q := ⟨⟨M, N, h1, h2⟩, h⟩

@[simp] theorem matR_mkPt (M N : Matrix (Fin (n + n)) (Fin (n + n)) (R ⊗[F] E)) (h1 : M * N = 1) (h2 : N * M = 1)
    (h : cT (sigR R σ) M * JR R Q * M = JR R Q) : matR R σ (mkPt R σ M N h1 h2 h) = M := rfl

variable {R σ} in

theorem cT_herm (b : HermR R σ n) : cT (sigR R σ) b.1 = b.1 := by
  ext i j; exact b.2 i j

variable (hQ : Q = StdUnn.blk4 0 1 (-1) 0)
include hQ

def nLoc (b : HermR R σ n) : HA R σ Q :=
  mkPt R σ (StdUnn.blk4 1 b.1 0 1) (StdUnn.blk4 1 (-b.1) 0 1)
    (by simp [StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.block_matrix_one])
    (by simp [StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.block_matrix_one])
    (by rw [JR_eq R hQ, cT_blk4, cT_one', cT_zero', cT_herm]
        simp [StdUnn.Model.submatrix_fromBlocks_mul])

def wLoc : HA R σ Q :=
  mkPt R σ (StdUnn.blk4 0 1 (-1) 0) (StdUnn.blk4 0 (-1) 1 0)
    (by simp [StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.block_matrix_one])
    (by simp [StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.block_matrix_one])
    (by rw [JR_eq R hQ, cT_blk4, cT_one', cT_zero', cT_neg_one]
        simp [StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.block_matrix_one])

theorem mat_nLoc (b : HermR R σ n) : matR R σ (nLoc R σ hQ b) = StdUnn.blk4 1 b.1 0 1 := rfl

theorem mat_wLoc : matR R σ (wLoc R σ hQ) = StdUnn.blk4 0 1 (-1) 0 := rfl

theorem nLoc_add (b b' : HermR R σ n) : nLoc R σ hQ (b + b') = nLoc R σ hQ b * nLoc R σ hQ b' :=
  ext_matR (by
    simp only [matR_mul, mat_nLoc, StdUnn.Model.submatrix_fromBlocks_mul, AddSubgroup.coe_add]
    simp [add_comm])

@[simp] theorem nLoc_zero : nLoc R σ hQ (0 : HermR R σ n) = 1 :=
  ext_matR (by rw [mat_nLoc, matR_one]; simpa using StdUnn.Model.block_matrix_one)

end Points

section Parabolic

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}
  (Q : Matrix (Fin (n + n)) (Fin (n + n)) E)

def upperHalfR : Submodule (R ⊗[F] E) (Fin (n + n) → R ⊗[F] E) :=
  LinearMap.ker (LinearMap.funLeft (R ⊗[F] E) (R ⊗[F] E) fun i : Fin n => finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n))

def upperParabolic : Subgroup (HA R σ Q) := (stabGL (upperHalfR (F := F) (E := E) R (n := n))).comap (matHom R σ Q)

variable {R σ Q}

theorem mem_upperHalfR {x : Fin (n + n) → R ⊗[F] E} :
    x ∈ upperHalfR R ↔ ∀ i : Fin n, x (finSumFinEquiv (Sum.inr i)) = 0 := by
  simp [upperHalfR, funext_iff, LinearMap.funLeft_apply]

theorem lower_eq_zero {p : HA R σ Q} (hp : p ∈ upperParabolic R σ Q) (i j : Fin n) :
    matR R σ p (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0 := by
  have h := (hp (Pi.single (finSumFinEquiv (.inl j)) 1)).1 (mem_upperHalfR.2 fun k => by
    have : (finSumFinEquiv (Sum.inr k : Fin n ⊕ Fin n)) ≠ finSumFinEquiv (.inl j) := by
      rw [Ne, finSumFinEquiv.apply_eq_iff_eq]; simp
    simp only [Pi.single_eq_of_ne this])
  have h2 := mem_upperHalfR.1 h i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, matR] using h2

theorem blkA_mulR {p q : HA R σ Q} (hq : q ∈ upperParabolic R σ Q) :
    StdUnn.blkA (matR R σ (p * q)) = StdUnn.blkA (matR R σ p) * StdUnn.blkA (matR R σ q) := by
  ext i j
  simp only [matR_mul, StdUnn.blkA, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [lower_eq_zero hq, mul_zero, Finset.sum_const_zero, add_zero]

variable (R σ Q)

def leviUp : upperParabolic R σ Q →* GL (Fin n) (R ⊗[F] E) :=
  MonoidHom.toHomUnits ⟨⟨fun p => StdUnn.blkA (matR R σ p.1), by
    rw [show ((1 : upperParabolic R σ Q) : HA R σ Q) = 1 from rfl, matR_one, StdUnn.blkA, Matrix.submatrix_one_equiv,
      ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]⟩, fun p q => blkA_mulR q.2⟩

def aUp : upperParabolic R σ Q →* (R ⊗[F] E)ˣ := Matrix.GeneralLinearGroup.det.comp (leviUp R σ Q)

variable {R σ Q}

theorem coe_leviUp (p : upperParabolic R σ Q) : (leviUp R σ Q p : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = StdUnn.blkA (matR R σ p.1) :=
  rfl

theorem coe_aUp (p : upperParabolic R σ Q) : (aUp R σ Q p : R ⊗[F] E) = (StdUnn.blkA (matR R σ p.1)).det := rfl

theorem mem_siegelParabolic_of_blockUpperTriangular {g : HA R σ Q} {a b d d' : Matrix (Fin n) (Fin n) (R ⊗[F] E)}
    (hg : matR R σ g = StdUnn.blk4 a b 0 d) (hd : d' * d = 1) : g ∈ upperParabolic R σ Q := fun x => by
  change x ∈ upperHalfR R ↔ matR R σ g *ᵥ x ∈ upperHalfR R
  simp only [mem_upperHalfR, hg, blockMatrix_mulVec_lower, Matrix.zero_mulVec, Pi.zero_apply, zero_add]
  constructor
  · intro h i
    rw [show (fun j => x (finSumFinEquiv (Sum.inr j))) = 0 from funext h, Matrix.mulVec_zero, Pi.zero_apply]
  · intro h i
    have e : (d *ᵥ fun j => x (finSumFinEquiv (Sum.inr j))) = 0 := funext h
    have := congrArg (d' *ᵥ ·) e
    simp only [Matrix.mulVec_mulVec, hd, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact congrFun this i

variable (hQ : Q = StdUnn.blk4 0 1 (-1) 0)
include hQ

theorem nLoc_mem_upP (b : HermR R σ n) : nLoc R σ hQ b ∈ upperParabolic R σ Q :=
  mem_siegelParabolic_of_blockUpperTriangular (mat_nLoc R σ hQ b) (Matrix.one_mul 1)

@[simp] theorem aUp_nLoc (b : HermR R σ n) : aUp R σ Q ⟨nLoc R σ hQ b, nLoc_mem_upP hQ b⟩ = 1 :=
  Units.ext (by rw [coe_aUp, mat_nLoc, upperLeft_blockMatrix, Matrix.det_one, Units.val_one])

end Parabolic

section More

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

variable {R σ} in

theorem cT_cT (hσ : ∀ x, σ (σ x) = x) (M : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    cT (sigR R σ) (cT (sigR R σ) M) = M := by
  ext i j; simp [cT, sigR_invol hσ]

def mLoc (hσ : ∀ x, σ (σ x) = x) (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (a : GL (Fin n) (R ⊗[F] E)) : HA R σ Q :=
  have e1 : cT (sigR R σ) a.1 * cT (sigR R σ) (a⁻¹).1 = 1 := by rw [← cT_mul, Units.inv_mul, cT_one']
  have e2 : cT (sigR R σ) (a⁻¹).1 * cT (sigR R σ) a.1 = 1 := by rw [← cT_mul, Units.mul_inv, cT_one']
  have e3 : cT (sigR R σ) (cT (sigR R σ) (a⁻¹).1) * a.1 = 1 := by rw [cT_cT hσ, Units.inv_mul]
  mkPt R σ (StdUnn.blk4 a.1 0 0 (cT (sigR R σ) (a⁻¹).1)) (StdUnn.blk4 (a⁻¹).1 0 0 (cT (sigR R σ) a.1))
    (by simp [StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.block_matrix_one, e2, -Matrix.coe_units_inv])
    (by simp [StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.block_matrix_one, e1, -Matrix.coe_units_inv])
    (by rw [JR_eq R hQ, cT_blk4, cT_zero']
        simp [StdUnn.Model.submatrix_fromBlocks_mul, e1, e3, -Matrix.coe_units_inv])

theorem mat_mLoc (hσ : ∀ x, σ (σ x) = x) (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (a : GL (Fin n) (R ⊗[F] E)) :
    matR R σ (mLoc R σ hσ hQ a) = StdUnn.blk4 a.1 0 0 (cT (sigR R σ) (a⁻¹).1) := rfl

theorem mLoc_mem_upP (hσ : ∀ x, σ (σ x) = x) (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (a : GL (Fin n) (R ⊗[F] E)) :
    mLoc R σ hσ hQ a ∈ upperParabolic R σ Q :=
  mem_siegelParabolic_of_blockUpperTriangular (mat_mLoc R σ hσ hQ a) (show cT (sigR R σ) a.1 * cT (sigR R σ) (a⁻¹).1 = 1 by
    rw [← cT_mul, Units.inv_mul, cT_one'])

@[simp] theorem aUp_mLoc (hσ : ∀ x, σ (σ x) = x) (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (a : GL (Fin n) (R ⊗[F] E)) :
    aUp R σ Q ⟨mLoc R σ hσ hQ a, mLoc_mem_upP R σ hσ hQ a⟩ = Matrix.GeneralLinearGroup.det a :=
  Units.ext (by rw [coe_aUp, mat_mLoc, upperLeft_blockMatrix]; rfl)

variable {R' : Type} [CommRing R'] [Algebra F R']

variable {R σ} in

theorem sigR_map (φ : R →ₐ[F] R') (y : R ⊗[F] E) :
    sigR R' σ (Algebra.TensorProduct.map φ (AlgHom.id F E) y) =
      Algebra.TensorProduct.map φ (AlgHom.id F E) (sigR R σ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {R σ} in

def hermMap (φ : R →ₐ[F] R') : HermR R σ n →+ HermR R' σ n where
  toFun b := ⟨b.1.map (Algebra.TensorProduct.map φ (AlgHom.id F E)), fun i j => by
    simp only [Matrix.map_apply, sigR_map, b.2 i j]⟩
  map_zero' := Subtype.ext (by ext i j; simp)
  map_add' b b' := Subtype.ext (by ext i j; simp)

variable (hQ : Q = StdUnn.blk4 0 1 (-1) 0)
include hQ

theorem mapH_nLoc (φ : R →ₐ[F] R') (b : HermR R σ n) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ Q φ (nLoc R σ hQ b) = nLoc R' σ hQ (hermMap φ b) := by
  refine ext_matR (Matrix.ext fun r s => (GlobalTheory.AutFunCompare.mat_mapH σ Q φ _ r s).trans ?_)
  have := congrFun (congrFun (blockMatrix_map (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom 1 b.1 0 1) r) s
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _)] at this
  exact this

theorem mapH_wLoc (φ : R →ₐ[F] R') : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ Q φ (wLoc R σ hQ) = wLoc R' σ hQ := by
  refine ext_matR (Matrix.ext fun r s => (GlobalTheory.AutFunCompare.mat_mapH σ Q φ _ r s).trans ?_)
  have := congrFun (congrFun (blockMatrix_map (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom 0 1 (-1) 0) r) s
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _),
    Matrix.map_neg _ (map_neg _), Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this

theorem continuous_nLoc [TopologicalSpace R] [IsTopologicalRing R] [FiniteDimensional F E] :
    Continuous (nLoc R σ hQ (n := n)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  rw [(isEmbedding_matHom R σ Q).continuous_iff, Units.continuous_iff]
  constructor
  · exact ((continuous_const.matrix_fromBlocks continuous_subtype_val continuous_const continuous_const).matrix_submatrix
      _ _ : Continuous fun b : HermR R σ n => StdUnn.blk4 1 b.1 0 1)
  · exact ((continuous_const.matrix_fromBlocks continuous_subtype_val.neg continuous_const continuous_const).matrix_submatrix
      _ _ : Continuous fun b : HermR R σ n => StdUnn.blk4 1 (-b.1) 0 1)

end More

section Parabolic2

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] {σ : E →ₐ[F] E} {n : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

theorem mulVec_mem_upperHalfR {M : Matrix (Fin (n + n)) (Fin (n + n)) (R ⊗[F] E)}
    (hM : ∀ i j : Fin n, M (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0) {x : Fin (n + n) → R ⊗[F] E}
    (hx : x ∈ upperHalfR R) : M *ᵥ x ∈ upperHalfR R := mem_upperHalfR.2 fun i => by
  simp only [Matrix.mulVec, dotProduct]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [hM, mem_upperHalfR.1 hx, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]

theorem mem_siegelParabolic_iff {g : HA R σ Q} : g ∈ upperParabolic R σ Q ↔ ∀ i j : Fin n,
    matR R σ g (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0 ∧
      matR R σ g⁻¹ (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0 := by
  refine ⟨fun h i j => ⟨lower_eq_zero h i j, lower_eq_zero (inv_mem h) i j⟩, fun h x =>
    ⟨mulVec_mem_upperHalfR fun i j => (h i j).1, fun hx => ?_⟩⟩
  have := mulVec_mem_upperHalfR (fun i j => (h i j).2) hx
  change matR R σ g⁻¹ *ᵥ (matR R σ g *ᵥ x) ∈ _ at this
  rwa [Matrix.mulVec_mulVec, ← matR_mul, inv_mul_cancel, matR_one, Matrix.one_mulVec] at this

theorem exists_blockMatrixTwoByTwoFin_eq {A : Type} (M : Matrix (Fin (n + n)) (Fin (n + n)) A) : ∃ a b c d, M = StdUnn.blk4 a b c d :=
  ⟨_, _, _, _, by
    rw [StdUnn.blk4, Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv), Matrix.submatrix_submatrix]
    simp⟩

theorem mem_siegelParabolic_iff_lowerLeft_eq_zero (hQ : Q = StdUnn.blk4 0 1 (-1) 0) {g : HA R σ Q} : g ∈ upperParabolic R σ Q ↔
    ∀ i j : Fin n, matR R σ g (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0 := by
  refine ⟨lower_eq_zero, fun h => ?_⟩
  obtain ⟨a, b, c, d, e⟩ := exists_blockMatrixTwoByTwoFin_eq (matR R σ g)
  obtain rfl : c = 0 := Matrix.ext fun i j => by
    have := h i j
    rwa [e, StdUnn.blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  have hu : cT (sigR R σ) (matR R σ g) * JR R Q * matR R σ g = JR R Q := g.2
  rw [JR_eq R hQ, e, cT_blk4, cT_zero', StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.submatrix_fromBlocks_mul] at hu
  exact mem_siegelParabolic_of_blockUpperTriangular e (d' := cT (sigR R σ) a) (by simpa using (StdUnn.Model.blockMatrixTwoByTwoFin_injective hu).2.1)

theorem wLoc_notMem_upP (hQ : Q = StdUnn.blk4 0 1 (-1) 0) [Nontrivial (R ⊗[F] E)] (hn : 0 < n) :
    wLoc R σ hQ ∉ upperParabolic R σ Q := fun h => by
  have := lower_eq_zero h ⟨0, hn⟩ ⟨0, hn⟩
  rw [mat_wLoc, StdUnn.blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  simp at this

theorem nLoc_injective (hQ : Q = StdUnn.blk4 0 1 (-1) 0) : Function.Injective (nLoc R σ hQ) := fun _ _ e =>
  Subtype.ext (StdUnn.Model.blockMatrixTwoByTwoFin_injective (congrArg (matR R σ) e)).2.1

theorem mLoc_mul (hσ : ∀ x, σ (σ x) = x) (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (a a' : GL (Fin n) (R ⊗[F] E)) :
    mLoc R σ hσ hQ (a * a') = mLoc R σ hσ hQ a * mLoc R σ hσ hQ a' :=
  ext_matR (by
    simp only [matR_mul, mat_mLoc, StdUnn.Model.submatrix_fromBlocks_mul, mul_inv_rev, Units.val_mul, cT_mul, mul_zero, zero_mul,
      add_zero, zero_add])

theorem mLoc_one (hσ : ∀ x, σ (σ x) = x) (hQ : Q = StdUnn.blk4 0 1 (-1) 0) :
    mLoc R σ hσ hQ (1 : GL (Fin n) (R ⊗[F] E)) = 1 :=
  ext_matR (by rw [mat_mLoc, inv_one, Units.val_one, cT_one', StdUnn.Model.block_matrix_one, matR_one])

variable {R' : Type} [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R')

theorem matR_mapH (g : HA R σ Q) : matR R' σ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ Q φ g) =
    (matR R σ g).map (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom :=
  Matrix.ext fun r s => GlobalTheory.AutFunCompare.mat_mapH σ Q φ g r s

theorem mapH_mem_upP {g : HA R σ Q} (hg : g ∈ upperParabolic R σ Q) : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ Q φ g ∈ upperParabolic R' σ Q :=
  mem_siegelParabolic_iff.2 fun i j => by
    rw [← map_inv, matR_mapH, matR_mapH, Matrix.map_apply, Matrix.map_apply, (mem_siegelParabolic_iff.1 hg i j).1,
      (mem_siegelParabolic_iff.1 hg i j).2, map_zero]
    exact ⟨rfl, rfl⟩

theorem aUp_mapH (p : upperParabolic R σ Q) : aUp R' σ Q ⟨GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ Q φ p, mapH_mem_upP φ p.2⟩ =
    Units.map (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom.toMonoidHom (aUp R σ Q p) :=
  Units.ext ((congrArg (fun M => (StdUnn.blkA M).det) (matR_mapH φ p.1)).trans
    (RingHom.map_det (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom (StdUnn.blkA (matR R σ p.1))).symm)

theorem mapH_mLoc (hσ : ∀ x, σ (σ x) = x) (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (a : GL (Fin n) (R ⊗[F] E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ Q φ (mLoc R σ hσ hQ a) =
      mLoc R' σ hσ hQ (bc (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom a) := by
  refine ext_matR ?_
  rw [matR_mapH, mat_mLoc, mat_mLoc, blockMatrix_map, Matrix.map_zero _ (map_zero _), ← map_inv]
  congr 1
  exact Matrix.ext fun i j => (sigR_map φ _).symm

variable [TopologicalSpace R]

theorem continuous_matR : Continuous (matR R σ (Q := Q)) :=
  Units.continuous_val.comp (isEmbedding_matHom R σ Q).continuous

variable [IsTopologicalRing R] [FiniteDimensional F E]

theorem continuous_leviUp : Continuous (leviUp R σ Q) := by
  have hA : Continuous fun g : HA R σ Q => StdUnn.blkA (matR R σ g) :=
    continuous_matrix fun i j => continuous_matR.matrix_elem _ _
  rw [Units.continuous_iff]
  refine ⟨hA.comp continuous_subtype_val, ?_⟩
  refine (hA.comp (continuous_subtype_val.comp continuous_inv)).congr fun p => ?_
  rw [← map_inv]; rfl

theorem continuous_aUp : Continuous (aUp R σ Q) := by
  haveI := isTopologicalRing_tens (F := F) (E := E) (R := R)
  have hd : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) (R ⊗[F] E) → (R ⊗[F] E)ˣ) := by
    rw [Units.continuous_iff]
    refine ⟨Units.continuous_val.matrix_det, (Units.continuous_coe_inv.matrix_det).congr fun g => ?_⟩
    rw [← map_inv]; rfl
  exact hd.comp continuous_leviUp

theorem isClosed_upP [T2Space R] : IsClosed (upperParabolic R σ Q : Set (HA R σ Q)) := by
  haveI := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := R)
  have : (upperParabolic R σ Q : Set (HA R σ Q)) = ⋂ i : Fin n, ⋂ j : Fin n,
      ({g | matR R σ g (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0} ∩
        {g | matR R σ g⁻¹ (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0}) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, SetLike.mem_coe, mem_siegelParabolic_iff]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => (isClosed_eq (continuous_matR.matrix_elem _ _) continuous_const).inter
    (isClosed_eq ((continuous_matR.comp continuous_inv).matrix_elem _ _) continuous_const)

end Parabolic2

section Sections

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}
  (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (ν : (R ⊗[F] E)ˣ →* ℝ≥0) (K : Subgroup (HA R σ Q))

abbrev IsIwasawaUp : Prop := IsIwasawa (ν.comp (aUp R σ Q)) K

def hgtUp : HA R σ Q → ℝ≥0 := iwAbs (ν.comp (aUp R σ Q)) K

def psUp [TopologicalSpace R] (μ : (R ⊗[F] E)ˣ →* Circle) (s : ℂ) : Submodule ℂ (HA R σ Q → ℂ) :=
  indSpace (ν.comp (aUp R σ Q)) K (μ.comp (aUp R σ Q)) (s + (n : ℂ) / 2)

def flatUp (Φ : HA R σ Q → ℂ) (s₀ s : ℂ) : HA R σ Q → ℂ := flatSec (ν.comp (aUp R σ Q)) K Φ s₀ s

def sphUp (s : ℂ) : HA R σ Q → ℂ := fun g => npow (hgtUp R σ Q ν K g) (s + (n : ℂ) / 2)

variable {Q} in

def intwLoc [TopologicalSpace R] (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (db : Measure (HermR R σ n)) (f : ℂ → HA R σ Q → ℂ)
    (s : ℂ) (g : HA R σ Q) : ℂ := ∫ b, f s (wLoc R σ hQ * nLoc R σ hQ b * g) ∂db

variable {Q} in

def IntwConv [TopologicalSpace R] (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (db : Measure (HermR R σ n)) (f : ℂ → HA R σ Q → ℂ)
    (s : ℂ) (g : HA R σ Q) : Prop := Integrable (fun b => f s (wLoc R σ hQ * nLoc R σ hQ b * g)) db

variable {R σ Q ν K}

theorem hgtUp_pos (g : HA R σ Q) : 0 < hgtUp R σ Q ν K g := iwAbs_pos _ K g

theorem flatUp_apply (Φ : HA R σ Q → ℂ) (s₀ s : ℂ) (g : HA R σ Q) :
    flatUp R σ Q ν K Φ s₀ s g = Φ g * npow (hgtUp R σ Q ν K g) (s - s₀) := rfl

@[simp] theorem flatUp_self (Φ : HA R σ Q → ℂ) (s₀ : ℂ) : flatUp R σ Q ν K Φ s₀ s₀ = Φ := flatSec_self Φ s₀

theorem flatUp_flatUp (Φ : HA R σ Q → ℂ) (s₀ s₁ s : ℂ) :
    flatUp R σ Q ν K (flatUp R σ Q ν K Φ s₀ s₁) s₁ s = flatUp R σ Q ν K Φ s₀ s := flatSec_flatSec Φ s₀ s₁ s

theorem sphUp_ne_zero (s : ℂ) (g : HA R σ Q) : sphUp R σ Q ν K s g ≠ 0 := npow_ne_zero (hgtUp_pos g) _

theorem flatUp_sphUp (s₀ s : ℂ) : flatUp R σ Q ν K (sphUp R σ Q ν K s₀) s₀ s = sphUp R σ Q ν K s := funext fun g => by
  rw [flatUp_apply, sphUp, sphUp, ← npow_add (hgtUp_pos g)]
  congr 1; ring

theorem hgtUp_mul (h : IsIwasawaUp R σ Q ν K) (p : upperParabolic R σ Q) {k : HA R σ Q} (hk : k ∈ K) :
    hgtUp R σ Q ν K (p * k) = ν (aUp R σ Q p) := h.iwAbs_mul p hk

theorem hgtUp_left (h : IsIwasawaUp R σ Q ν K) (p : upperParabolic R σ Q) (g : HA R σ Q) :
    hgtUp R σ Q ν K (p * g) = ν (aUp R σ Q p) * hgtUp R σ Q ν K g := h.iwAbs_left p g

theorem hgtUp_right (h : IsIwasawaUp R σ Q ν K) (g : HA R σ Q) {k : HA R σ Q} (hk : k ∈ K) :
    hgtUp R σ Q ν K (g * k) = hgtUp R σ Q ν K g := h.iwAbs_right g hk

theorem hgtUp_of_mem (h : IsIwasawaUp R σ Q ν K) {k : HA R σ Q} (hk : k ∈ K) : hgtUp R σ Q ν K k = 1 := h.iwAbs_of_mem hk

theorem sphUp_of_mem (h : IsIwasawaUp R σ Q ν K) (s : ℂ) {k : HA R σ Q} (hk : k ∈ K) : sphUp R σ Q ν K s k = 1 := by
  rw [sphUp, hgtUp_of_mem h hk, one_npow]

theorem hgtUp_mLoc (h : IsIwasawaUp R σ Q ν K) (hσ : ∀ x, σ (σ x) = x) (hQ : Q = StdUnn.blk4 0 1 (-1) 0)
    (a : GL (Fin n) (R ⊗[F] E)) : hgtUp R σ Q ν K (mLoc R σ hσ hQ a) = ν (Matrix.GeneralLinearGroup.det a) :=
  (h.iwAbs_coe ⟨_, mLoc_mem_upP R σ hσ hQ a⟩).trans (congrArg ν (aUp_mLoc R σ hσ hQ a))

variable [TopologicalSpace R]

theorem mem_psUp {μ : (R ⊗[F] E)ˣ →* Circle} {s : ℂ} {Φ : HA R σ Q → ℂ} : Φ ∈ psUp R σ Q ν K μ s ↔
    (∀ (p : upperParabolic R σ Q) (g : HA R σ Q),
      Φ (p * g) = μ (aUp R σ Q p) * npow (ν (aUp R σ Q p)) (s + (n : ℂ) / 2) * Φ g) ∧ Continuous Φ ∧ IsKFinite K Φ :=
  Iff.rfl

theorem apply_nLoc_mul (hQ : Q = StdUnn.blk4 0 1 (-1) 0) {μ : (R ⊗[F] E)ˣ →* Circle} {s : ℂ} {Φ : HA R σ Q → ℂ}
    (hΦ : Φ ∈ psUp R σ Q ν K μ s) (b : HermR R σ n) (g : HA R σ Q) : Φ (nLoc R σ hQ b * g) = Φ g := by
  simpa using (mem_psUp.1 hΦ).1 ⟨_, nLoc_mem_upP hQ b⟩ g

theorem apply_mLoc_mul (hσ : ∀ x, σ (σ x) = x) (hQ : Q = StdUnn.blk4 0 1 (-1) 0) {μ : (R ⊗[F] E)ˣ →* Circle} {s : ℂ}
    {Φ : HA R σ Q → ℂ} (hΦ : Φ ∈ psUp R σ Q ν K μ s) (a : GL (Fin n) (R ⊗[F] E)) (g : HA R σ Q) :
    Φ (mLoc R σ hσ hQ a * g) = μ (Matrix.GeneralLinearGroup.det a) *
      npow (ν (Matrix.GeneralLinearGroup.det a)) (s + (n : ℂ) / 2) * Φ g := by
  simpa only [aUp_mLoc] using (mem_psUp.1 hΦ).1 ⟨_, mLoc_mem_upP R σ hσ hQ a⟩ g

theorem intwLoc_eq (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (db : Measure (HermR R σ n)) (f : ℂ → HA R σ Q → ℂ) (s : ℂ)
    (g : HA R σ Q) : intwLoc R σ hQ db f s g = ∫ b, f s (wLoc R σ hQ * nLoc R σ hQ b * g) ∂db := rfl

theorem intwConv_iff (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (db : Measure (HermR R σ n)) (f : ℂ → HA R σ Q → ℂ) (s : ℂ)
    (g : HA R σ Q) :
    IntwConv R σ hQ db f s g ↔ Integrable (fun b => f s (wLoc R σ hQ * nLoc R σ hQ b * g)) db := Iff.rfl

theorem intwLoc_add (hQ : Q = StdUnn.blk4 0 1 (-1) 0) {db : Measure (HermR R σ n)} {f f' : ℂ → HA R σ Q → ℂ} {s : ℂ}
    {g : HA R σ Q} (h : IntwConv R σ hQ db f s g) (h' : IntwConv R σ hQ db f' s g) :
    intwLoc R σ hQ db (f + f') s g = intwLoc R σ hQ db f s g + intwLoc R σ hQ db f' s g := integral_add h h'

theorem intwLoc_nLoc_mul [IsTopologicalRing R] [FiniteDimensional F E] (hQ : Q = StdUnn.blk4 0 1 (-1) 0)
    (db : Measure (HermR R σ n)) [db.IsAddRightInvariant] (f : ℂ → HA R σ Q → ℂ) (s : ℂ) (b₀ : HermR R σ n)
    (g : HA R σ Q) : intwLoc R σ hQ db f s (nLoc R σ hQ b₀ * g) = intwLoc R σ hQ db f s g := by
  haveI := isTopologicalRing_tens (F := F) (E := E) (R := R)
  haveI : BorelSpace (HermR R σ n) := ⟨rfl⟩
  rw [intwLoc, intwLoc, ← integral_add_right_eq_self (fun b => f s (wLoc R σ hQ * nLoc R σ hQ b * g)) b₀]
  simp only [nLoc_add, mul_assoc]

variable [IsTopologicalRing R] [FiniteDimensional F E] [T2Space R]

theorem hgtUp_mul_of_isCompact (hν : Continuous ν) (hK : IsCompact (K : Set (HA R σ Q))) (p : upperParabolic R σ Q) {k : HA R σ Q}
    (hk : k ∈ K) : hgtUp R σ Q ν K (p * k) = ν (aUp R σ Q p) :=
  iwAbs_mul_of_triv (triv_of_isCompact (δ := ν.comp (aUp R σ Q)) isClosed_upP (hν.comp continuous_aUp) hK) p hk

theorem isIwasawaUp_of_isCompact (hν : Continuous ν) (hK : IsCompact (K : Set (HA R σ Q)))
    (h : ∀ g : HA R σ Q, ∃ p : upperParabolic R σ Q, ∃ k ∈ K, g = p * k) : IsIwasawaUp R σ Q ν K :=
  isIwasawa_of_isCompact isClosed_upP (hν.comp continuous_aUp) hK h

theorem continuous_hgtUp (h : IsIwasawaUp R σ Q ν K) (hν : Continuous ν) (hK : IsCompact (K : Set (HA R σ Q))) :
    Continuous (hgtUp R σ Q ν K) := h.continuous_iwAbs isClosed_upP (hν.comp continuous_aUp) hK

theorem sphUp_mem (h : IsIwasawaUp R σ Q ν K) (hν : Continuous ν) (hK : IsCompact (K : Set (HA R σ Q))) (s : ℂ) :
    sphUp R σ Q ν K s ∈ psUp R σ Q ν K 1 s := h.npow_iwAbs_mem isClosed_upP (hν.comp continuous_aUp) hK _

theorem flatUp_mem (h : IsIwasawaUp R σ Q ν K) (hν : Continuous ν) (hK : IsCompact (K : Set (HA R σ Q)))
    {μ : (R ⊗[F] E)ˣ →* Circle} {s₀ : ℂ} {Φ : HA R σ Q → ℂ} (hΦ : Φ ∈ psUp R σ Q ν K μ s₀) (s : ℂ) :
    flatUp R σ Q ν K Φ s₀ s ∈ psUp R σ Q ν K μ s := h.flatSec_mem isClosed_upP (hν.comp continuous_aUp) hK hΦ s

end Sections

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (Q : Matrix (Fin (n + n)) (Fin (n + n)) E)

abbrev KUpFin (v : HeightOneSpectrum (𝓞 F)) : Subgroup (GLoc σ Q v) := stabLoc σ Q (stdLattice E (n + n)) v

abbrev KUpArch (w : InfinitePlace F) : Subgroup (GArch σ Q w) := stabArch σ Q w 1

abbrev KUpAd : Subgroup (GAd σ Q) := levelAll σ Q (stdLattice E (n + n)) 1

variable {σ Q}

section

omit [NumberField E]

theorem mem_KUpAd {g : GAd σ Q} : g ∈ KUpAd σ Q ↔
    (∀ v, proj σ Q v g ∈ KUpFin σ Q v) ∧ ∀ w, projArch σ Q w g ∈ KUpArch σ Q w := by
  simp only [mem_levelAll, map_one]

theorem emb_mem_KUpAd {v : HeightOneSpectrum (𝓞 F)} {k : GLoc σ Q v} (hk : k ∈ KUpFin σ Q v) : emb σ Q v k ∈ KUpAd σ Q :=
  mem_KUpAd.2 ⟨fun u => by
    by_cases e : u = v
    · subst e; simpa using hk
    · simp [proj_emb_ne σ Q e], fun w => by simp⟩

theorem embArch_mem_KUpAd {w : InfinitePlace F} {k : GArch σ Q w} (hk : k ∈ KUpArch σ Q w) :
    embArch σ Q w k ∈ KUpAd σ Q :=
  mem_KUpAd.2 ⟨fun u => by simp, fun u => by
    by_cases e : u = w
    · subst e; simpa using hk
    · simp [projArch_embArch_ne σ Q e]⟩

theorem proj_nLoc (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (v : HeightOneSpectrum (𝓞 F)) (b : HermR (AF F) σ n) :
    proj σ Q v (nLoc _ σ hQ b) = nLoc _ σ hQ (hermMap (evFin F v) b) := mapH_nLoc _ σ hQ _ b

theorem projArch_nLoc (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (w : InfinitePlace F) (b : HermR (AF F) σ n) :
    projArch σ Q w (nLoc _ σ hQ b) = nLoc _ σ hQ (hermMap (evInf F w) b) := mapH_nLoc _ σ hQ _ b

theorem proj_wLoc (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (v : HeightOneSpectrum (𝓞 F)) :
    proj σ Q v (wLoc _ σ hQ) = wLoc _ σ hQ := mapH_wLoc _ σ hQ _

theorem projArch_wLoc (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (w : InfinitePlace F) :
    projArch σ Q w (wLoc _ σ hQ) = wLoc _ σ hQ := mapH_wLoc _ σ hQ _

def projUp (v : HeightOneSpectrum (𝓞 F)) : upperParabolic (AF F) σ Q →* upperParabolic (Fv F v) σ Q :=
  ((proj σ Q v).comp (Subgroup.subtype _)).codRestrict _ fun p => mapH_mem_upP _ p.2

def projArchUp (w : InfinitePlace F) : upperParabolic (AF F) σ Q →* upperParabolic w.Completion σ Q :=
  ((projArch σ Q w).comp (Subgroup.subtype _)).codRestrict _ fun p => mapH_mem_upP _ p.2

@[simp] theorem coe_projUp (v : HeightOneSpectrum (𝓞 F)) (p : upperParabolic (AF F) σ Q) :
    (projUp v p : GLoc σ Q v) = proj σ Q v p := rfl

@[simp] theorem coe_projArchUp (w : InfinitePlace F) (p : upperParabolic (AF F) σ Q) :
    (projArchUp w p : GArch σ Q w) = projArch σ Q w p := rfl

theorem aUp_projUp (v : HeightOneSpectrum (𝓞 F)) (p : upperParabolic (AF F) σ Q) :
    aUp _ σ Q (projUp v p) = unitFin F E v (aUp _ σ Q p) := aUp_mapH _ p

theorem aUp_projArchUp (w : InfinitePlace F) (p : upperParabolic (AF F) σ Q) :
    aUp _ σ Q (projArchUp w p) = unitInf F E w (aUp _ σ Q p) := aUp_mapH _ p

theorem exists_mul_fin (hI : ∀ g : GAd σ Q, ∃ p : upperParabolic (AF F) σ Q, ∃ k ∈ KUpAd σ Q, g = p * k)
    (v : HeightOneSpectrum (𝓞 F)) (g : GLoc σ Q v) : ∃ p : upperParabolic (Fv F v) σ Q, ∃ k ∈ KUpFin σ Q v, g = p * k := by
  obtain ⟨p, k, hk, e⟩ := hI (emb σ Q v g)
  exact ⟨projUp v p, _, (mem_KUpAd.1 hk).1 v, by rw [coe_projUp, ← map_mul, ← e, proj_emb_self]⟩

theorem exists_mul_arch (hI : ∀ g : GAd σ Q, ∃ p : upperParabolic (AF F) σ Q, ∃ k ∈ KUpAd σ Q, g = p * k)
    (w : InfinitePlace F) (g : GArch σ Q w) : ∃ p : upperParabolic w.Completion σ Q, ∃ k ∈ KUpArch σ Q w, g = p * k := by
  obtain ⟨p, k, hk, e⟩ := hI (embArch σ Q w g)
  exact ⟨projArchUp w p, _, (mem_KUpAd.1 hk).2 w, by rw [coe_projArchUp, ← map_mul, ← e, projArch_embArch_self]⟩

end

theorem mem_siegelParabolic_iff_forall_place {g : GAd σ Q} : g ∈ upperParabolic (AF F) σ Q ↔
    (∀ w, projArch σ Q w g ∈ upperParabolic _ σ Q) ∧ ∀ v, proj σ Q v g ∈ upperParabolic _ σ Q := by
  refine ⟨fun h => ⟨fun w => mapH_mem_upP _ h, fun v => mapH_mem_upP _ h⟩, fun h => mem_siegelParabolic_iff.2 fun i j =>
    ⟨adele_ext (fun w => ?_) fun v => ?_, adele_ext (fun w => ?_) fun v => ?_⟩⟩
  · rw [map_zero]; exact (mem_siegelParabolic_iff.1 (h.1 w) i j).1
  · rw [map_zero]; exact (mem_siegelParabolic_iff.1 (h.2 v) i j).1
  · rw [map_zero]; exact (mem_siegelParabolic_iff.1 (h.1 w) i j).2
  · rw [map_zero]; exact (mem_siegelParabolic_iff.1 (h.2 v) i j).2

def embUp (v : HeightOneSpectrum (𝓞 F)) : upperParabolic (Fv F v) σ Q →* upperParabolic (AF F) σ Q :=
  ((emb σ Q v).comp (Subgroup.subtype _)).codRestrict _ fun p => mem_siegelParabolic_iff_forall_place.2
    ⟨fun w => by simp, fun u => by
      by_cases e : u = v
      · subst e; simp
      · simp [proj_emb_ne σ Q e]⟩

def embArchUp (w : InfinitePlace F) : upperParabolic w.Completion σ Q →* upperParabolic (AF F) σ Q :=
  ((embArch σ Q w).comp (Subgroup.subtype _)).codRestrict _ fun p => mem_siegelParabolic_iff_forall_place.2
    ⟨fun u => by
      by_cases e : u = w
      · subst e; simp
      · simp [projArch_embArch_ne σ Q e], fun u => by simp⟩

@[simp] theorem coe_embUp (v : HeightOneSpectrum (𝓞 F)) (p : upperParabolic (Fv F v) σ Q) :
    (embUp v p : GAd σ Q) = emb σ Q v p := rfl

@[simp] theorem coe_embArchUp (w : InfinitePlace F) (p : upperParabolic w.Completion σ Q) :
    (embArchUp w p : GAd σ Q) = embArch σ Q w p := rfl

theorem aUp_embUp (v : HeightOneSpectrum (𝓞 F)) (p : upperParabolic (Fv F v) σ Q) :
    aUp _ σ Q (embUp v p) = ideleAt F E v (aUp _ σ Q p) :=
  idele_ext (fun w => by
    rw [← aUp_projArchUp, unitInf_ideleAt, show projArchUp w (embUp v p) = 1 from Subtype.ext (by simp), map_one])
    fun u => by
    rw [← aUp_projUp]
    by_cases e : u = v
    · subst e; rw [unitFin_ideleAt_self, show projUp u (embUp u p) = p from Subtype.ext (by simp)]
    · rw [unitFin_ideleAt_ne e, show projUp u (embUp v p) = 1 from Subtype.ext (proj_emb_ne σ Q e _), map_one]

theorem aUp_embArchUp (w : InfinitePlace F) (p : upperParabolic w.Completion σ Q) :
    aUp _ σ Q (embArchUp w p) = ideleAtInf F E w (aUp _ σ Q p) :=
  idele_ext (fun u => by
    rw [← aUp_projArchUp]
    by_cases e : u = w
    · subst e; rw [unitInf_ideleAtInf_self, show projArchUp u (embArchUp u p) = p from Subtype.ext (by simp)]
    · rw [unitInf_ideleAtInf_ne e, show projArchUp u (embArchUp w p) = 1 from
        Subtype.ext (projArch_embArch_ne σ Q e _), map_one]) fun v => by
    rw [← aUp_projUp, unitFin_ideleAtInf, show projUp v (embArchUp w p) = 1 from Subtype.ext (by simp), map_one]

theorem isCompact_KUpFin (v : HeightOneSpectrum (𝓞 F)) : IsCompact (KUpFin σ Q v : Set (GLoc σ Q v)) :=
  haveI : Submodule.IsLattice E (stdLattice E (n + n)) := isLattice_stdLattice
  isCompact_stabLoc σ Q _ v

theorem isOpen_KUpFin (v : HeightOneSpectrum (𝓞 F)) : IsOpen (KUpFin σ Q v : Set (GLoc σ Q v)) :=
  haveI : Submodule.IsLattice E (stdLattice E (n + n)) := isLattice_stdLattice
  isOpen_stabLoc σ Q _ v

theorem isCompact_KUpArch (hc : IsCMExt F E σ) (w : InfinitePlace F) : IsCompact (KUpArch σ Q w : Set (GArch σ Q w)) :=
  Frames.isCompact_stabArch hc Q w _

theorem isCompact_KUpAd (hc : IsCMExt F E σ) : IsCompact (KUpAd σ Q : Set (GAd σ Q)) :=
  haveI : Submodule.IsLattice E (stdLattice E (n + n)) := isLattice_stdLattice
  isCompact_levelAll hc Q _ _

theorem eventually_proj_mem_KUpFin (g : GAd σ Q) : ∀ᶠ v in Filter.cofinite, proj σ Q v g ∈ KUpFin σ Q v :=
  haveI : Submodule.IsLattice E (stdLattice E (n + n)) := isLattice_stdLattice
  eventually_proj_mem_stabLoc σ Q _ g

theorem finite_mulSupport_hgtUp (g : GAd σ Q) :
    (Function.mulSupport fun v => hgtUp _ σ Q (absEv F E v) (KUpFin σ Q v) (proj σ Q v g)).Finite :=
  (Filter.eventually_cofinite.1 (eventually_proj_mem_KUpFin g)).subset fun v hv h' => hv (by
    simpa using hgtUp_mul_of_isCompact (continuous_absEv v) (isCompact_KUpFin v) 1 h')

variable (hc : IsCMExt F E σ) (hI : ∀ g : GAd σ Q, ∃ p : upperParabolic (AF F) σ Q, ∃ k ∈ KUpAd σ Q, g = p * k)

include hI in

theorem isIwasawaUp_fin_of (v : HeightOneSpectrum (𝓞 F)) : IsIwasawaUp _ σ Q (absEv F E v) (KUpFin σ Q v) :=
  isIwasawaUp_of_isCompact (continuous_absEv v) (isCompact_KUpFin v) (exists_mul_fin hI v)

include hc hI

theorem isIwasawaUp_arch_of (w : InfinitePlace F) : IsIwasawaUp _ σ Q (absEw F E w) (KUpArch σ Q w) :=
  isIwasawaUp_of_isCompact (continuous_absEw w) (isCompact_KUpArch hc w) (exists_mul_arch hI w)

theorem isIwasawaUp_ad_of : IsIwasawaUp _ σ Q (absE F E) (KUpAd σ Q) :=
  haveI := t2Space_adeleRing' (F := F)
  isIwasawaUp_of_isCompact continuous_absE (isCompact_KUpAd hc) hI

theorem hgtUp_ad_eq_of (g : GAd σ Q) : hgtUp _ σ Q (absE F E) (KUpAd σ Q) g =
    (∏ w, hgtUp _ σ Q (absEw F E w) (KUpArch σ Q w) (projArch σ Q w g)) *
      ∏ᶠ v, hgtUp _ σ Q (absEv F E v) (KUpFin σ Q v) (proj σ Q v g) := by
  obtain ⟨p, k, hk, rfl⟩ := hI g
  rw [hgtUp_mul (isIwasawaUp_ad_of hc hI) p hk, absE_apply]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => by
      rw [map_mul, ← coe_projArchUp, hgtUp_mul (isIwasawaUp_arch_of hc hI w) _ ((mem_KUpAd.1 hk).2 w), aUp_projArchUp]
  · exact finprod_congr fun v => by
      rw [map_mul, ← coe_projUp, hgtUp_mul (isIwasawaUp_fin_of hI v) _ ((mem_KUpAd.1 hk).1 v), aUp_projUp]

end Places

section Datum

open Formalism.BasicNotions Formalism.L2.Theta Formalism.IndefR.Datum

variable (D : D7) (n : ℕ)

theorem Jst_eq : StdUnn.Jst D n = StdUnn.blk4 0 1 (-1) 0 := rfl

theorem upperParabolic_adele : upperParabolic (AF D.host.F) D.sp.cm.sig (StdUnn.Jst D n) = StdUnn.P D n := rfl

theorem KUpAd_adele : KUpAd D.sp.cm.sig (StdUnn.Jst D n) = StdUnn.K D n := rfl

variable {D n} in

theorem matR_adele (g : StdUnn.G D n) : matR (AF D.host.F) D.sp.cm.sig g = StdUnn.mat g := rfl

theorem exists_mul_adele (g : StdUnn.G D n) : ∃ p : upperParabolic (AF D.host.F) D.sp.cm.sig (StdUnn.Jst D n),
    ∃ k ∈ KUpAd D.sp.cm.sig (StdUnn.Jst D n), g = p * k := by
  obtain ⟨p, hp, k, hk, e⟩ := StdUnn.Iwasawa.exists_mul D n g
  exact ⟨⟨p, hp⟩, k, hk, e⟩

theorem isIwasawaUp_fin (v : HeightOneSpectrum (𝓞 D.host.F)) :
    IsIwasawaUp _ D.sp.cm.sig (StdUnn.Jst D n) (absEv D.host.F D.host.E v) (KUpFin _ _ v) :=
  isIwasawaUp_fin_of (exists_mul_adele D n) v

theorem isIwasawaUp_arch (w : InfinitePlace D.host.F) :
    IsIwasawaUp _ D.sp.cm.sig (StdUnn.Jst D n) (absEw D.host.F D.host.E w) (KUpArch _ _ w) :=
  isIwasawaUp_arch_of (isCMExt_host D) (exists_mul_adele D n) w

theorem isIwasawaUp_ad : IsIwasawaUp _ D.sp.cm.sig (StdUnn.Jst D n) (absA D) (StdUnn.K D n) :=
  isIwasawaUp_ad_of (isCMExt_host D) (exists_mul_adele D n)

theorem sphUp_mem_fin (v : HeightOneSpectrum (𝓞 D.host.F)) (s : ℂ) :
    sphUp _ D.sp.cm.sig (StdUnn.Jst D n) (absEv D.host.F D.host.E v) (KUpFin _ _ v) s ∈
      psUp _ D.sp.cm.sig (StdUnn.Jst D n) (absEv D.host.F D.host.E v) (KUpFin _ _ v) 1 s :=
  sphUp_mem (isIwasawaUp_fin D n v) (continuous_absEv v) (isCompact_KUpFin v) s

theorem sphUp_mem_arch (w : InfinitePlace D.host.F) (s : ℂ) :
    sphUp _ D.sp.cm.sig (StdUnn.Jst D n) (absEw D.host.F D.host.E w) (KUpArch _ _ w) s ∈
      psUp _ D.sp.cm.sig (StdUnn.Jst D n) (absEw D.host.F D.host.E w) (KUpArch _ _ w) 1 s :=
  sphUp_mem (isIwasawaUp_arch D n w) (continuous_absEw w) (isCompact_KUpArch (isCMExt_host D) w) s

variable {D n} in

theorem isHeight_iff {H : StdUnn.G D n → ℝ≥0} :
    StdUnn.IsHeight H ↔ H = hgtUp _ D.sp.cm.sig (StdUnn.Jst D n) (absA D) (StdUnn.K D n) := by
  constructor
  · intro h
    funext g
    obtain ⟨p, k, hk, rfl⟩ := exists_mul_adele D n g
    rw [hgtUp_mul (isIwasawaUp_ad D n) p hk]
    exact h p p.2 (leviUp _ _ _ p) rfl k hk
  · rintro rfl p hp a ha k hk
    rw [show a = leviUp (AF D.host.F) D.sp.cm.sig (StdUnn.Jst D n) ⟨p, hp⟩ from Units.ext ha.symm]
    exact hgtUp_mul (isIwasawaUp_ad D n) ⟨p, hp⟩ hk

variable {D n} in

theorem isHeight_eq_prod {H : StdUnn.G D n → ℝ≥0} (h : StdUnn.IsHeight H) (g : StdUnn.G D n) : H g =
    (∏ w, hgtUp _ D.sp.cm.sig (StdUnn.Jst D n) (absEw D.host.F D.host.E w) (KUpArch _ _ w) (projArch _ _ w g)) *
      ∏ᶠ v, hgtUp _ D.sp.cm.sig (StdUnn.Jst D n) (absEv D.host.F D.host.E v) (KUpFin _ _ v) (proj _ _ v g) := by
  rw [isHeight_iff.1 h]
  exact hgtUp_ad_eq_of (isCMExt_host D) (exists_mul_adele D n) g

theorem hermN_eq : ResAniso.hermN D n = HermR (AF D.host.F) D.sp.cm.sig n :=
  AddSubgroup.ext fun _ => Matrix.ext_iff.symm

def hermAddEquiv : ResAniso.hermN D n ≃+ HermR (AF D.host.F) D.sp.cm.sig n := AddEquiv.addSubgroupCongr (hermN_eq D n)

theorem continuous_hermAddEquiv : Continuous (hermAddEquiv D n) := continuous_subtype_val.subtype_mk _

theorem continuous_hermAddEquiv_symm : Continuous (hermAddEquiv D n).symm := continuous_subtype_val.subtype_mk _

def hermEquiv : ResAniso.hermN D n ≃ᵐ HermR (AF D.host.F) D.sp.cm.sig n where
  toEquiv := (hermAddEquiv D n).toEquiv
  measurable_toFun :=
    haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
    haveI : BorelSpace (HermR (AF D.host.F) D.sp.cm.sig n) := ⟨rfl⟩
    (continuous_hermAddEquiv D n).measurable
  measurable_invFun :=
    haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
    haveI : BorelSpace (HermR (AF D.host.F) D.sp.cm.sig n) := ⟨rfl⟩
    (continuous_hermAddEquiv_symm D n).measurable

variable {D n}

@[simp] theorem coe_hermEquiv (b : ResAniso.hermN D n) : (hermEquiv D n b).1 = b.1 := rfl

@[simp] theorem coe_hermEquiv_symm (b : HermR (AF D.host.F) D.sp.cm.sig n) : ((hermEquiv D n).symm b).1 = b.1 := rfl

theorem hermEquiv_eq (b : ResAniso.hermN D n) : hermEquiv D n b = hermAddEquiv D n b := rfl

theorem isAddHaarMeasure_map_hermEquiv (db : Measure (ResAniso.hermN D n)) [db.IsAddHaarMeasure] :
    (db.map (hermEquiv D n)).IsAddHaarMeasure := by
  obtain ⟨i1, -⟩ := GlobalTheory.MixModel.lattice_Mx D n n
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : BorelSpace (HermR (AF D.host.F) D.sp.cm.sig n) := ⟨rfl⟩
  exact (hermAddEquiv D n).isAddHaarMeasure_map db (continuous_hermAddEquiv D n) (continuous_hermAddEquiv_symm D n)

theorem nElt_eq (b : ResAniso.hermN D n) :
    ResAniso.nElt b = nLoc (AF D.host.F) D.sp.cm.sig (Jst_eq D n) (hermEquiv D n b) :=
  ext_matR (ResAniso.mat_nElt b)

theorem wElt_eq : ResAniso.wElt D n = wLoc (AF D.host.F) D.sp.cm.sig (Jst_eq D n) := ext_matR (ResAniso.mat_wElt D n)

theorem intw_eq (db : Measure (ResAniso.hermN D n)) (f : ℂ → StdUnn.G D n → ℂ) (s : ℂ) (g : StdUnn.G D n) :
    ResAniso.intw db f s g = intwLoc (AF D.host.F) D.sp.cm.sig (Jst_eq D n) (db.map (hermEquiv D n)) f s g := by
  rw [intwLoc, (hermEquiv D n).measurableEmbedding.integral_map]
  simp only [ResAniso.intw, nElt_eq, wElt_eq]

theorem intwConv_map_iff (db : Measure (ResAniso.hermN D n)) (f : ℂ → StdUnn.G D n → ℂ) (s : ℂ) (g : StdUnn.G D n) :
    IntwConv (AF D.host.F) D.sp.cm.sig (Jst_eq D n) (db.map (hermEquiv D n)) f s g ↔
      Integrable (fun b => f s (ResAniso.wElt D n * ResAniso.nElt b * g)) db := by
  rw [IntwConv, (hermEquiv D n).measurableEmbedding.integrable_map_iff]
  simp only [nElt_eq, wElt_eq]
  rfl

end Datum

section Tests

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = StdUnn.blk4 0 1 (-1) 0)

example : matR R σ (wLoc R σ hQ * wLoc R σ hQ) = StdUnn.blk4 (-1) 0 0 (-1) := by
  simp [matR_mul, mat_wLoc, StdUnn.Model.submatrix_fromBlocks_mul]

example (b : HermR R σ n) : matR R σ (wLoc R σ hQ * nLoc R σ hQ b) = StdUnn.blk4 0 1 (-1) (-b.1) := by
  simp [matR_mul, mat_wLoc, mat_nLoc, StdUnn.Model.submatrix_fromBlocks_mul]

example (hσ : ∀ x, σ (σ x) = x) (a : GL (Fin n) (R ⊗[F] E)) (b b' : HermR R σ n)
    (h : b'.1 = a.1 * b.1 * cT (sigR R σ) a.1) :
    mLoc R σ hσ hQ a * nLoc R σ hQ b = nLoc R σ hQ b' * mLoc R σ hσ hQ a :=
  ext_matR (by
    simp only [matR_mul, mat_mLoc, mat_nLoc, StdUnn.Model.submatrix_fromBlocks_mul, h, mul_zero, zero_mul, add_zero, zero_add, mul_one,
      one_mul]
    rw [mul_assoc _ (cT _ _), ← cT_mul, Units.inv_mul, cT_one', mul_one])

example [TopologicalSpace R] [MeasurableSingletonClass (HermR R σ n)] (f : ℂ → HA R σ Q → ℂ) (s : ℂ) (g : HA R σ Q) :
    IntwConv R σ hQ (Measure.dirac 0) f s g ∧ intwLoc R σ hQ (Measure.dirac 0) f s g = f s (wLoc R σ hQ * g) :=
  ⟨integrable_dirac (by simp), by rw [intwLoc, integral_dirac, nLoc_zero, mul_one]⟩

end Tests

end GlobalTheory.LocIntw

end
