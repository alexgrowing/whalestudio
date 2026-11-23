import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordsAlongOrthonormalRealSubfieldBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugateStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem U_pullB_eq_prod (D : D7) (hG : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b) (g : ℂ → ℂ) (t z : VC D N N') :
    U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b g) z =
      ∏ j, U1 (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) g (coordB D (tor0 D cc δ) b j z) := by
  obtain ⟨-, -, hP, -, -⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG cc δ N N' r b hb
  unfold U U1 pullB Hf
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hP, hP]
  congr 1
  · exact Finset.prod_congr rfl fun j _ => by rw [coordB_add]
  · congr 1
    simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [tor0]
    ring

theorem normalisedThetaPullback_mem_torsionTranslatesSpan (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (t0 : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (N N' r : ℕ)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b) :
    pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) ∈ Tr D (tor0 D cc δ) b := by
  have hG : admG1 D := (GlobalTheory.InducedType.induced_type D).1
  have hgood := isTraceCompatibleTorusEmbedding_standardTorus D hG cc δ
  obtain ⟨-, -, -, hL, -⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG cc δ N N' r b hb
  set t : VC D N N' := ∑ j, (fun _ : Fin r => t0) j • embV D (tor0 D cc δ) (b j) with htdef
  have hco : ∀ j, coordB D (tor0 D cc δ) b j t = t0 := fun j => hgood.coordB_sum hb.1 _ j
  have h2 : (2 : ℕ) • t ∈ LaB D (tor0 D cc δ) b := by
    rw [hL]
    intro k
    rw [two_nsmul, coordB_add, hco, ← two_mul]
    exact ht.1
  have hq : U1 (lamOf D cc δ) t0 (sgStar (lamOf D cc δ)) 0 ∈ Qbar := by
    have := (GlobalTheory.T.forall_use1 D cc δ hc).1 t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ 0
    simpa [coef1] using this
  have hmem : U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) ∈
      Tr D (tor0 D cc δ) b := Submodule.subset_span ⟨t, ⟨2, two_pos, h2⟩, rfl⟩
  have := Submodule.smul_mem _
    (⟨(U1 (lamOf D cc δ) t0 (sgStar (lamOf D cc δ)) 0)⁻¹ ^ r, pow_mem (inv_mem hq) r⟩ : Qbar) hmem
  convert this using 1
  funext z
  change _ = (U1 (lamOf D cc δ) t0 (sgStar (lamOf D cc δ)) 0)⁻¹ ^ r *
    U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) z
  rw [U_pullB_eq_prod D hG cc δ b hb]
  simp only [hco, pullB, GL3Theta.th0, div_eq_inv_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

end GlobalTheory.ThetaConj
