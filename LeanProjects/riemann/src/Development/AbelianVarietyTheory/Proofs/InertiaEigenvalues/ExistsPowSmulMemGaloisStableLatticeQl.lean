import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulMemLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.TContMul

variable {l : ℕ} [Fact l.Prime]

theorem exists_pow_smul_mem (LL : FinExt l) (T : QLat LL) (v : T.V)
    (hv : v ∈ Submodule.span ↥LL.1 (T.L.T : Set T.V)) : ∃ n : ℕ, ((l : ↥LL.1) ^ n) • v ∈ T.L.T := by
  first
  | exact @_root_.GlobalTheory.LatticePowerScalar.exists_pow_smul_mem_lattice
  | exact _root_.GlobalTheory.LatticePowerScalar.exists_pow_smul_mem_lattice
  | (apply _root_.GlobalTheory.LatticePowerScalar.exists_pow_smul_mem_lattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticePowerScalar.exists_pow_smul_mem_lattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticePowerScalar.exists_pow_smul_mem_lattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticePowerScalar.exists_pow_smul_mem_lattice ..)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (v : T.V), ∃ n : ℕ, ∃ x ∈ T.L.T, x = ((l : ↥LL.1) ^ n) • v := by
  intro l _ LL T v
  have hv : v ∈ Submodule.span ↥LL.1 (T.L.T : Set T.V) := by rw [T.L.span]; trivial
  obtain ⟨n, hn⟩ := exists_pow_smul_mem LL T v hv
  exact ⟨n, _, hn, rfl⟩

end GlobalTheory.TContMul
