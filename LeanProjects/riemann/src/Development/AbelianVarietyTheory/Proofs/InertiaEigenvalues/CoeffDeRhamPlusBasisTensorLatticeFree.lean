import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LinearIndependentQlProductBasisOfZlLattice
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LatticeActionMemFilZeroDeRham
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsBdRPlusCoeffsOfMemFilZeroDeRham
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
theorem _root_.GlobalTheory.T.coeffDeRhamPlus_basis_tensorLattice_free : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (κ : Type) [Fintype κ] (b : Module.Basis κ ↥(OL LL) ↥T.L.T), (∀ v : T.V ⊗[ℚ_[l]] Pl.R.BdR, v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) ↔ ∃ d : κ → OD l ↥(OL LL), v = ∑ k, act (d k) (((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR))) ∧ ∀ d : κ → OD l ↥(OL LL), ∑ k, act (d k) (((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) = 0 → ∀ k, d k = 0 := by
  intro l _ LL T Pl AI Td act hA κ _ b
  refine ⟨fun v => ⟨UpperTheory.KN.exists_BdRPlus_coeffs_of_mem_filZero_deRham l LL T Pl AI Td act hA κ b v, ?_⟩,
    UpperTheory.KN.linearIndependent_Ql_productBasis_of_Zl_lattice l LL T Pl AI Td act hA κ b⟩
  rintro ⟨d, rfl⟩
  exact Submodule.sum_mem _ fun k _ => UpperTheory.KN.latticeAction_mem_filZero_deRham l LL T Pl AI Td act hA (d k) _
