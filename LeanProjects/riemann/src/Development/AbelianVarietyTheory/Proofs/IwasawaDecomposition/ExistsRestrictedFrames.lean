import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NuInRange
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalRingCardinality.Lemmas
import Formalism.LocalToGlobal.Divisibility.FramesLemmas

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.Mem

theorem cnorm_mulVec_eq_of_gram {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (M : Matrix ι μ ℂ) (N : Matrix κ μ ℂ) (h : Mᴴ * M = Nᴴ * N) (u : μ → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (M.mulVec u) = Formalism.HermitianLatticesTheory.cnorm (N.mulVec u) := by
  have key : ∀ {ι : Type} [Fintype ι] (M : Matrix ι μ ℂ),
      ((∑ i, ‖M.mulVec u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ (Mᴴ * M).mulVec u := by
    intro ι _ M
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    push_cast
    simp only [dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.star_def, Complex.conj_mul']
  have h2 : (∑ i, ‖M.mulVec u i‖ ^ 2 : ℝ) = ∑ i, ‖N.mulVec u i‖ ^ 2 := by
    have := key M
    rw [h, ← key N] at this
    exact_mod_cast this
  unfold Formalism.HermitianLatticesTheory.cnorm
  rw [h2]

theorem exists_restricted_frames : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (A : HLat K)
    (U : Submodule K A.V) (L : Submodule (𝓞 K) U), (∀ v, IsUnit (A.X v).det) →
    ∃ (n : ℕ) (b : Module.Basis (Fin n) K U) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
      (∀ v, IsUnit (X v).det) ∧
        ∀ v (x : U), Formalism.HermitianLatticesTheory.normAt b X v x = Formalism.HermitianLatticesTheory.normAt A.b A.X v (x : A.V) := by
  intro K _ _ _ A U _ hX
  have : Module.Finite K A.V := Module.Finite.of_basis A.b
  let n := Module.finrank K U
  let b : Module.Basis (Fin n) K U := Module.finBasis K U
  let E : Matrix A.ι (Fin n) K := LinearMap.toMatrix b A.b U.subtype
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective U.subtype U.ker_subtype
  have hLE : LinearMap.toMatrix A.b b g * E = 1 := by
    rw [← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
  let M : InfinitePlace K → Matrix A.ι (Fin n) ℂ := fun v => (A.X v)⁻¹ * E.map v.embedding
  have hM : ∀ v, Function.Injective (M v).mulVec := by
    intro v x y hxy
    have h1 : ((LinearMap.toMatrix A.b b g).map v.embedding * A.X v) * M v = 1 := by
      simp only [M]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A.X v), Matrix.mul_nonsing_inv _ (hX v),
        Matrix.one_mul, ← Matrix.map_mul, hLE, Formalism.L2.DIV.map_one']
    have := congrArg ((LinearMap.toMatrix A.b b g).map v.embedding * A.X v).mulVec hxy
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.one_mulVec] at this
  have hP : ∀ v, ((M v)ᴴ * M v).PosDef := fun v => Matrix.PosDef.conjTranspose_mul_self _ (hM v)
  refine ⟨n, b, fun v => Formalism.L2.DIV.frameOf ((M v)ᴴ * M v),
    fun v => (Formalism.L2.DIV.frameOfSpec n _ (hP v)).1, fun v x => ?_⟩
  have h2 := (Formalism.L2.DIV.frameOfSpec n _ (hP v)).2
  have h3 : Formalism.HermitianLatticesTheory.vecAt A.b v (x : A.V) = (E.map v.embedding).mulVec (Formalism.HermitianLatticesTheory.vecAt b v x) := by
    have h4 := LinearMap.toMatrix_mulVec_repr b A.b U.subtype x
    funext i
    have h5 := congrFun h4 i
    simp only [Submodule.subtype_apply] at h5
    simp only [Formalism.HermitianLatticesTheory.vecAt]
    rw [← h5]
    simp [Matrix.mulVec, dotProduct, E, Formalism.HermitianLatticesTheory.vecAt]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
  rw [h3, Matrix.mulVec_mulVec]
  exact cnorm_mulVec_eq_of_gram _ _ h2 _

end GlobalTheory.Mem

end
