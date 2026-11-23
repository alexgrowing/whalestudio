import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticPairingRankOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_pairing_rank_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (ξ : Fin n → E) (y : Fin n → AE F E), symp (cA σ) (-1) (incM F X.J) (incM F W.J) (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (Matrix.vecMulVec y (incV F H'.x)) = Algebra.trace (AF F) (AE F E) (∑ i, incV F ξ i * (incM F X.J *ᵥ fun k => cA σ (y k)) i) := by
  first | exact @GlobalTheory.ThK.IsoSymp.symp_iso_term | exact GlobalTheory.ThK.IsoSymp.symp_iso_term | (intros; apply GlobalTheory.ThK.IsoSymp.symp_iso_term <;> assumption)
