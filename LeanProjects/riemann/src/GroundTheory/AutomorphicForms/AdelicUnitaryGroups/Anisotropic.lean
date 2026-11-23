import Mathlib
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Topology

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct Topology Metric

noncomputable section

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Form

variable (K) (H : Matrix ι ι E) (R : Type*) [CommRing R] [Algebra K R]

def hermValue (x : ι → R ⊗[K] E) : R ⊗[K] E :=
  (fun i => conjBase K E R (x i)) ⬝ᵥ (baseMatrix K H R *ᵥ x)

variable {K H R}

theorem hermValue_mulVec (g : unitaryPoints K E H R) (x : ι → R ⊗[K] E) :
    hermValue K H R (unitaryMat g *ᵥ x) = hermValue K H R x := by
  have hg : ((unitaryMat g).map (conjBase K E R))ᵀ * baseMatrix K H R * unitaryMat g =
      baseMatrix K H R := g.2
  have h1 : (fun i => conjBase K E R ((unitaryMat g *ᵥ x) i)) =
      (unitaryMat g).map (conjBase K E R) *ᵥ (fun i => conjBase K E R (x i)) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  unfold hermValue
  rw [h1, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg, Matrix.dotProduct_mulVec]

theorem conjBase_smul (c : R) (z : R ⊗[K] E) :
    conjBase K E R (c • z) = c • conjBase K E R z :=
  map_smul (show R ⊗[K] E →ₐ[R] R ⊗[K] E from
    Algebra.TensorProduct.map (AlgHom.id R R) (conj K E).toAlgHom) c z

theorem hermValue_smul (c : R) (x : ι → R ⊗[K] E) :
    hermValue K H R (c • x) = (c * c) • hermValue K H R x := by
  unfold hermValue
  have : (fun i => conjBase K E R ((c • x) i)) = c • fun i => conjBase K E R (x i) := by
    funext i
    simp only [Pi.smul_apply, conjBase_smul]
  rw [this, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul]

end Form

section Compact

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

variable (H : Matrix ι ι E)
variable (R : Type*) [NontriviallyNormedField R] [ProperSpace R] [Algebra K R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

def anisoVecCoords (x : ι → R ⊗[K] E) : ι × κ → R :=
  fun p => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2

def anisoVecOfCoords (y : ι × κ → R) : ι → R ⊗[K] E :=
  fun i => (tensorCoordsHomeomorph R b).symm fun k => y (i, k)

variable {R b}

variable (R b)

def anisoForm (y : ι × κ → R) : κ → R :=
  tensorCoordsHomeomorph R b (hermValue K H R (anisoVecOfCoords R b y))

variable {H R b}

variable (H R)

end Compact

section RealPlace

open NumberField

variable (H : Matrix ι ι E)

abbrev completionNontriviallyNormedField (w : InfinitePlace K) :
    NontriviallyNormedField w.Completion :=
  { (inferInstance : NormedField w.Completion) with
    non_trivial := ⟨2, by
      have := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _) 2
      rw [← this, map_ofNat]
      norm_num⟩ }

def IsHermDefiniteAt (w : InfinitePlace K) (hw : w.IsReal) : Prop :=
  (∀ x : ι → w.Completion ⊗[K] E, x ≠ 0 → ∃ t : w.Completion,
      hermValue K H w.Completion x = algebraMap w.Completion (w.Completion ⊗[K] E) t ∧
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw t) ∨
    ∀ x : ι → w.Completion ⊗[K] E, x ≠ 0 → ∃ t : w.Completion,
      hermValue K H w.Completion x = algebraMap w.Completion (w.Completion ⊗[K] E) t ∧
        InfinitePlace.Completion.extensionEmbeddingOfIsReal hw t < 0

variable {H}

variable (H)

end RealPlace

end

end GroundTheory.Automorphic
