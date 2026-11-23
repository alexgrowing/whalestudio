import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem invariants_and_trace_of_card_eq_finrank :
    ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R] [Module.Free A R] [Module.Finite A R] (G : Finset (R →ₐ[A] R)), G.card = Module.finrank A R → (∀ x : R, (∀ g ∈ G, g x = x) → x ∈ (algebraMap A R).range) ∧ ∀ x : R, algebraMap A R (Algebra.trace A R x) = ∑ g ∈ G, g x := by
  classical
  intro A R _ _ _ _ _ _ _ G hG
  let b : Module.Basis G A R := (Module.finBasis A R).reindex
    (Fintype.equivOfCardEq (by simp [hG]))
  let M : Matrix G G R := Matrix.of fun g i => g.1 (b i)
  have hdet : M.det ≠ 0 := by
    intro h
    obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
    have hli : LinearIndependent R (fun g : G => ((g.1 : R →* R) : R → R)) := by
      refine (linearIndependent_monoidHom R R).comp (fun g : G => (g.1 : R →* R)) ?_
      intro g g' hgg
      apply Subtype.ext
      ext x
      exact DFunLike.congr_fun hgg x
    apply hv
    funext g
    refine Fintype.linearIndependent_iff.1 hli v ?_ g
    have hz : (∑ g : G, v g • g.1.toLinearMap) = 0 := by
      apply b.ext
      intro i
      have := congrFun hvM i
      simpa [Matrix.vecMul, dotProduct, M] using this
    funext x
    have := LinearMap.congr_fun hz x
    simpa using this
  have key : ∀ x : R, Matrix.diagonal (fun g : G => g.1 x) * M =
      M * (Algebra.leftMulMatrix b x).map (algebraMap A R) := by
    intro x
    ext g j
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [M, Matrix.of_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
    rw [← map_mul]
    conv_lhs => rw [← b.sum_repr (x * b j)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.smul_def, mul_comm]
  have key2 : ∀ x : R, M.adjugate * (Matrix.diagonal (fun g : G => g.1 x) * M) =
      M.det • (Algebra.leftMulMatrix b x).map (algebraMap A R) := by
    intro x
    rw [key, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  refine ⟨fun x hx => ?_, fun x => ?_⟩
  · obtain ⟨i⟩ : Nonempty G := b.index_nonempty
    have h1 : Matrix.diagonal (fun g : G => g.1 x) = x • (1 : Matrix G G R) := by
      rw [Matrix.smul_one_eq_diagonal]
      congr 1
      funext g
      exact hx g.1 g.2
    have h2 := key2 x
    rw [h1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.adjugate_mul] at h2
    have h3 := congrFun (congrFun h2 i) i
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, _root_.mul_one,
      Matrix.map_apply] at h3
    rw [mul_comm] at h3
    exact ⟨_, (mul_left_cancel₀ hdet h3).symm⟩
  · have h2 := congrArg Matrix.trace (key2 x)
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul,
      Matrix.mul_one, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
      Matrix.trace_diagonal] at h2
    have h3 := mul_left_cancel₀ hdet h2
    rw [Algebra.trace_eq_matrix_trace b, ← Finset.sum_coe_sort G (fun g => g x), h3]
    simp [Matrix.trace]

end GlobalTheory.PlaceInt
