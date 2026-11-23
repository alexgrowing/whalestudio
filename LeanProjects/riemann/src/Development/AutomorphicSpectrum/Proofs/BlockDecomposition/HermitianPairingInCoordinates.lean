import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordForm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianCoordinatesHomeomorph

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.PairCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_mul_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x y : E) :
    Algebra.trace F E (σ x * y) = Algebra.trace F E (x * σ y) := by
  have hinv : Function.Involutive σ := GlobalTheory.CompanionTheory.SiegelND.Coef.sig_invol h
  have key := Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective σ hinv.bijective) (σ x * y)
  rw [← key]
  simp [hinv x]

theorem trace_sigR_mul {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (u w : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ u * w) =
      ∑ k, (Algebra.TensorProduct.basis R b).repr u k *
        ∑ l, algebraMap F R (Algebra.trace F E (b k * σ (b l))) * (Algebra.TensorProduct.basis R b).repr w l := by
  set C := Algebra.TensorProduct.basis R b with hC
  have hC' : ∀ (r : R) (k : Fin d), r • C k = r ⊗ₜ[F] b k := by
    intro r k
    simp [hC, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  conv_lhs => rw [← C.sum_repr u, ← C.sum_repr w]
  simp only [hC', map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hs : sigR R σ (C.repr u k ⊗ₜ[F] b k) = C.repr u k ⊗ₜ[F] σ (b k) := by simp [sigR]
  rw [hs, Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.GaussMean.OneVec.trace_tmul, trace_mul_sig h]
  ring

theorem mulVec_inl (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) {n : ℕ} (v : Idx n d → R) (i : Fin n) :
    (((coordForm σ b n).map (algebraMap F R)).mulVec v) (Sum.inl i) = v (Sum.inl i) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, coordForm, Matrix.one_apply]

theorem mulVec_inr (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) {n : ℕ} (v : Idx n d → R) (k : Fin d)
    (q : {p : Fin n × Fin n // p.1 < p.2}) :
    (((coordForm σ b n).map (algebraMap F R)).mulVec v) (Sum.inr (k, q)) =
      ∑ l, algebraMap F R (Algebra.trace F E (b k * σ (b l))) * v (Sum.inr (l, q)) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, coordForm, Matrix.map_apply,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, map_zero, zero_mul,
    Finset.sum_const_zero, zero_add, Matrix.blockDiagonal_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single q]
  · simp
  · intro x _ hx
    simp [hx, Ne.symm hx]
  · simp

theorem pairHerm_eq_coordForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (d : ℕ)
    (b : Module.Basis (Fin d) F E) (n : ℕ) (S T : HermR R σ n),
    pairHerm R σ n S T = dotProduct (hCo R σ b S) (((coordForm σ b n).map (algebraMap F R)).mulVec (hCo R σ b T)) := by
  intro F E _ _ _ _ _ σ h R _ _ d b n S T
  rw [GlobalTheory.HermCoordEquiv.pair_eq R h S T]
  unfold GlobalTheory.HermSD.coordPair
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [mulVec_inl, Fintype.sum_prod_type, mulVec_inr]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [trace_sigR_mul h]
  rfl

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.PairCoord
