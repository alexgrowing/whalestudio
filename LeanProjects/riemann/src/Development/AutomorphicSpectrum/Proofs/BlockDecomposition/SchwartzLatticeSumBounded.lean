import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSummableBoundSchwartzMajorantRationalTransStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold

private theorem exists_isCompact_sub_incA_mem (D : D7) :
    ∃ C : Set (AE D), IsCompact C ∧ ∀ z : AE D, ∃ x : D.host.E, z - incA D x ∈ C := by
  classical
  obtain ⟨K0, hK0, hK0'⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele D.host.F
  let b := Module.finBasis D.host.F D.host.E
  let bA := Algebra.TensorProduct.basis (AF D.host.F) b
  let e : AE D ≃ₗ[AF D.host.F] (Fin (Module.finrank D.host.F D.host.E) → AF D.host.F) := bA.equivFun
  have he : Continuous e.symm :=
    IsModuleTopology.continuous_of_linearMap
      (e.symm : (Fin (Module.finrank D.host.F D.host.E) → AF D.host.F) →ₗ[AF D.host.F] AE D)
  have h1 : ∀ x : Fin (Module.finrank D.host.F D.host.E) → D.host.F,
      e.symm (fun i => algebraMap D.host.F (AF D.host.F) (x i)) = incA D (∑ i, x i • b i) := by
    intro x
    rw [show incA D (∑ i, x i • b i) = (1 : AF D.host.F) ⊗ₜ[D.host.F] (∑ i, x i • b i) from rfl,
      TensorProduct.tmul_sum]
    simp only [e, Module.Basis.equivFun_symm_apply, bA, Algebra.TensorProduct.basis_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [algebraMap_smul, TensorProduct.tmul_smul]
  refine ⟨e.symm '' Set.univ.pi (fun _ => K0), (isCompact_univ_pi fun _ => hK0).image he, ?_⟩
  intro z
  choose x hx using fun i => hK0' (e z i)
  refine ⟨∑ i, x i • b i, fun i => e z i - algebraMap D.host.F (AF D.host.F) (x i), fun i _ => hx i, ?_⟩
  have hv : (fun i => e z i - algebraMap D.host.F (AF D.host.F) (x i)) =
      e z - fun i => algebraMap D.host.F (AF D.host.F) (x i) := rfl
  rw [hv, map_sub, LinearEquiv.symm_apply_apply, h1]

theorem schwartzA_continuous_and_tsum_enorm_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ), φ ∈ schwartzA θ m n →
    Continuous φ ∧ ∃ B : ℝ≥0, ∀ w : Mx D m n, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖φ (rat ξ + w)‖ₑ ≤ B := by
  intro D θ hθ m n φ hφ
  have hSB := GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n φ hφ
  obtain ⟨hcont, K, hK, hKb⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ m n φ hSB
  refine ⟨hcont, ?_⟩
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ m n
  obtain ⟨C, hC, hCz⟩ := exists_isCompact_sub_incA_mem D
  choose xf hxf using hCz
  let Q : Set (Mx D m n) := {w | ∀ i j, w i j ∈ C}
  have hQ : IsCompact Q := by
    have h := isCompact_univ_pi (fun (_ : Fin m) => isCompact_univ_pi (fun (_ : Fin n) => hC))
    have hQeq : Q = (Set.univ.pi fun (_ : Fin m) => Set.univ.pi fun (_ : Fin n) => C) := by
      ext w
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [hQeq]
    exact h
  obtain ⟨b, hbs, hb⟩ := hN K Q hK hQ
  obtain ⟨c, hc⟩ := hKb N
  set c' : ℝ := max c 0 with hc'
  refine ⟨Real.toNNReal (c' * ∑' ξ, b ξ), fun w => ?_⟩
  let ξ0 : Matrix (Fin m) (Fin n) D.host.E := Matrix.of fun i j => xf (w i j)
  let x0 : Mx D m n := w - rat ξ0
  have hx0 : x0 ∈ Q := fun i j => hxf (w i j)
  have hb0 : ∀ ξ, 0 ≤ b ξ := fun ξ => (GlobalTheory.Unf.maj_nonneg θ K N _).trans (hb x0 hx0 ξ)
  have hrat : ∀ ξ, rat ξ + w = x0 + rat (ξ + ξ0) := by
    intro ξ
    ext i j
    simp only [x0, rat, Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, map_add]
    abel
  have hpt : ∀ ξ, ‖φ (rat ξ + w)‖ₑ ≤ ENNReal.ofReal (c' * b (ξ + ξ0)) := by
    intro ξ
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [hrat ξ]
    calc ‖φ (x0 + rat (ξ + ξ0))‖ ≤ c * GlobalTheory.Unf.maj θ K N (x0 + rat (ξ + ξ0)) := hc _
      _ ≤ c' * GlobalTheory.Unf.maj θ K N (x0 + rat (ξ + ξ0)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (GlobalTheory.Unf.maj_nonneg _ _ _ _)
      _ ≤ c' * b (ξ + ξ0) := mul_le_mul_of_nonneg_left (hb x0 hx0 _) (le_max_right _ _)
  calc ∑' ξ, ‖φ (rat ξ + w)‖ₑ ≤ ∑' ξ, ENNReal.ofReal (c' * b (ξ + ξ0)) := ENNReal.tsum_le_tsum hpt
    _ = ∑' η, ENNReal.ofReal (c' * b η) :=
      (Equiv.addRight ξ0).tsum_eq (fun η => ENNReal.ofReal (c' * b η))
    _ = ENNReal.ofReal (∑' η, c' * b η) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun η => mul_nonneg (le_max_right _ _) (hb0 η)) (hbs.mul_left c')).symm
    _ = ((Real.toNNReal (c' * ∑' ξ, b ξ) : ℝ≥0) : ℝ≥0∞) := by
      rw [tsum_mul_left]
      rfl

end GlobalTheory.CompanionTheory.EisUnfold
