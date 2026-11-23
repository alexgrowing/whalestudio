import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicPlaneVanishesAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTransposeInjective

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_isotropic_plane_vanishes_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁),
    form σ JW H'.x H'.x = 0 → ∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))),
      ∀ u' ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), symp (cA σ) (-1) (incM F JX) (incM F JW) u u' = 0 := by
  first | exact @GlobalTheory.MixedLagr.symplectic_isotropic_plane_vanishes | exact GlobalTheory.MixedLagr.symplectic_isotropic_plane_vanishes | (intros; apply GlobalTheory.MixedLagr.symplectic_isotropic_plane_vanishes <;> assumption)
