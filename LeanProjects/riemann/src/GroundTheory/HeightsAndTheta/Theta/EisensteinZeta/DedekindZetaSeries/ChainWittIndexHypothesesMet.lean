import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.DedekindZetaSeries.HeightGeSecondCubicBound
import GroundTheory.HeightsAndTheta.Theta.Signature
import GroundTheory.HeightsAndTheta.Theta.Parabolic
import GroundTheory.AutomorphicForms.HermitianDisc
import GroundTheory.HeightsAndTheta.Theta.GaussianExample
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open Module NumberField GroundTheory.Automorphic

universe u

def ChainWittIndex.Statement (F E : Type u) [Field F] [NumberField F] [IsTotallyReal F]
    [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ P : ChainParams, ∀ j : ℕ, j ≤ P.m →
    ∀ (V : Type u) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (h : HermitianForm F E V) (b : Basis (Fin (P.rk j)) E V),
      (∀ v : InfinitePlace F, signature h v = (P.rk j - P.nu j, P.nu j)) →
      wittIndex F (gram h.toSesq b) = P.nu j

instance isTotallyComplex_gaussQ : IsTotallyComplex GaussQ where
  isComplex v := by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff]
    intro hv
    set φ := v.embedding
    have hsq : φ (QuadraticAlgebra.omega) * φ (QuadraticAlgebra.omega) = -1 := by
      rw [← map_mul, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
      simp
    have him : (φ (QuadraticAlgebra.omega)).im = 0 := by
      have := RingHom.congr_fun hv (QuadraticAlgebra.omega)
      rw [ComplexEmbedding.conjugate_coe_eq] at this
      exact Complex.conj_eq_iff_im.1 this
    have hre := congrArg Complex.re hsq
    simp only [Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re, Complex.one_re] at hre
    nlinarith [mul_self_nonneg (φ (QuadraticAlgebra.omega)).re]

def chainWittExampleSigns : Fin 3 → ℚˣ := ![1, 1, -1]

noncomputable def chainWittExampleForm : HermitianForm ℚ GaussQ (Fin 3 → GaussQ) :=
  diagForm chainWittExampleSigns

end GroundTheory.Heights₂.Theta
