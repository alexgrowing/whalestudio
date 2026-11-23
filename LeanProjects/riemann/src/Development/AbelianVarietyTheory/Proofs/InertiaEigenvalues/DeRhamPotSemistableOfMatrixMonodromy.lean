import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicAdmissibleSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvertibleDeRhamPeriodMatrixOfIsDRStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableOfInvertiblePeriodMatrixSemistableRiStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotentiallySemistableOfSemistableRestrictStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.FromMat

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
  {n : Type} [Fintype n] [DecidableEq n]

def matRep (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l) :=
  MonoidHom.toHomUnits
    ((((algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)).mapMatrix : Matrix n n ℚ_[l] →+* Matrix n n ↥(MaximalUnramifiedExtension l)) :
        Matrix n n ℚ_[l] →* Matrix n n ↥(MaximalUnramifiedExtension l)).comp
      (((LinearMap.toMatrixAlgEquiv b : (V →ₗ[ℚ_[l]] V) ≃ₐ[ℚ_[l]] Matrix n n ℚ_[l]) :
        (V →ₗ[ℚ_[l]] V) →* Matrix n n ℚ_[l]).comp ρ))

theorem matRep_apply (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) (g : ↥(GK K)) (i j : n) :
    (matRep b ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j = algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (b.repr (ρ g (b j)) i) := by
  simp [matRep, LinearMap.toMatrixAlgEquiv_apply]

theorem toMatrix_map_apply (b : Module.Basis n ℚ_[l] V) (f : V →ₗ[ℚ_[l]] V) {A : Type} [Semiring A] [Algebra ℚ_[l] A]
    (i j : n) : (LinearMap.toMatrix b b f).map (algebraMap ℚ_[l] A) i j = algebraMap ℚ_[l] A (b.repr (f (b j)) i) := by
  simp [LinearMap.toMatrix_apply]

end GlobalTheory.PMon.FromMat

namespace GlobalTheory.PMon.FromMat

open GlobalTheory.PMon.Inhab

theorem deRhamPotSemistable_of_matThm : MatThm → GlobalTheory.Published.DeRhamPotSemistable := by
  intro hM l _ P AI hT K V _ _ _ _ _ ρ hc hDR
  obtain ⟨T⟩ := hT
  let b := Module.finBasis ℚ_[l] V
  have hR : IsRat 1 (matRep b ρ) := by
    refine ⟨one_pos, fun c hc' => ?_, fun g i j => ?_, fun i j => ?_⟩
    · obtain ⟨q, rfl⟩ := fixed_frob P c (by rwa [fr_one] at hc')
      exact K.1.algebraMap_mem q
    · rw [matRep_apply, fr_q]
    · simp only [matRep_apply]
      have h1 : Continuous fun g : ↥(GK K) => b.coord i (ρ g (b j)) :=
        (IsModuleTopology.continuous_of_linearMap (R := ℚ_[l]) (b.coord i)).comp (hc (b j))
      exact (continuous_algebraMap ℚ_[l] (Om l)).comp h1
  have hD : AdmDR P (matRep b ρ) := by
    intro m
    obtain ⟨Q, hQ⟩ := GlobalTheory.T.exists_invertible_deRhamPeriodMatrix_of_isDR l P AI T _ K V b ρ hDR
    refine ⟨Q, fun g => ?_⟩
    convert hQ g using 2
    refine Matrix.ext fun i j => ?_
    rw [matD, Matrix.map_apply, matRep_apply, fr_q, kd_alg, toMatrix_map_apply]
  obtain ⟨K', hK, Q, hQ⟩ := hM l P AI T _ K 1 (matRep b ρ) hR hD
  have hS : IsSst P (resTo ρ hK) := by
    refine GlobalTheory.T.isSemistable_of_invertible_periodMatrix_semistableRing l P AI T _ K' V b (resTo ρ hK) Q fun g => ?_
    convert hQ g using 2
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    rw [matRep_apply, LinearMap.toMatrix_apply, ks, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
      Polynomial.algebraMap_apply]
    rfl
  exact GlobalTheory.T.isPotentiallySemistable_of_semistable_restrict l P AI T K K' hK V ρ hS

end GlobalTheory.PMon.FromMat

end
