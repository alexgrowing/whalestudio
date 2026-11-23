import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta

theorem norm_eq_normSq_embU : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ κ : Kˣ,
  (((Units.map (Algebra.norm ℚ : K →* ℚ) κ : ℚˣ) : ℚ) : ℝ) = ‖((embU κ : ℂˣ) : ℂ)‖ ^ 2 ∧
  ((RationalIdeles.realPart (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) : ℝˣ) : ℝ) = ‖((embU κ : ℂˣ) : ℂ)‖ ^ 2 := by
  classical
  intro K _ _ h2 hc κ
  set w := Classical.arbitrary (InfinitePlace K) with hw
  set φ : K →+* ℂ := w.embedding with hφ
  have hne : ComplexEmbedding.conjugate φ ≠ φ := by
    intro h
    exact (InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex w))
      (ComplexEmbedding.isReal_iff.2 h)
  let σ : K →ₐ[ℚ] ℂ := φ.toRatAlgHom
  let σ' : K →ₐ[ℚ] ℂ := (ComplexEmbedding.conjugate φ).toRatAlgHom
  have hσ : σ ≠ σ' := by
    intro h
    apply hne
    ext x
    exact (DFunLike.congr_fun h x).symm
  have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = 2 := by
    rw [AlgHom.card, h2]
  have huniv : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) = {σ, σ'} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hσ, hcard]
  have hN : ((Algebra.norm ℚ (κ : K) : ℚ) : ℂ) = φ κ * (starRingEnd ℂ) (φ κ) := by
    have := Algebra.norm_eq_prod_embeddings ℚ ℂ (κ : K)
    rw [huniv, Finset.prod_pair hσ] at this
    simpa [σ, σ', ComplexEmbedding.conjugate_coe_eq] using this
  have hemb : ((embU κ : ℂˣ) : ℂ) = φ κ := rfl
  have hR : (((Algebra.norm ℚ (κ : K) : ℚ)) : ℝ) = ‖φ κ‖ ^ 2 := by
    have h3 : (((((Algebra.norm ℚ (κ : K) : ℚ)) : ℝ)) : ℂ) = ((‖φ κ‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_ratCast, hN, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast h3
  have h1 : (((Units.map (Algebra.norm ℚ : K →* ℚ) κ : ℚˣ) : ℚ) : ℝ) = ‖((embU κ : ℂˣ) : ℂ)‖ ^ 2 := by
    rw [hemb]
    exact hR
  refine ⟨h1, ?_⟩
  rw [← h1]
  exact RationalIdeles.realPart_diagonal _

end GlobalTheory.CompanionTheory.FexTheta
