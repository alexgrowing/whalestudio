import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory

theorem conj_norm_eq_of_minpoly_root :
    ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (z z' : Om l),
    Polynomial.aeval z' (minpoly (↥(Kunr l a)) z) = 0 → ‖z'‖ = ‖z‖ := by
  intro l _ a _ z z' h
  have hint : IsIntegral (↥(Kunr l a)) z := Algebra.IsIntegral.isIntegral z
  have hm : minpoly (↥(Kunr l a)) z' = minpoly (↥(Kunr l a)) z :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) h (minpoly.monic hint)).symm
  obtain ⟨τ, hτ⟩ := ((Normal.minpoly_eq_iff_mem_orbit (Om l)).1 hm)
  have hτ' : τ • z = z' := hτ
  rw [← hτ']
  exact (spectralNorm_eq_of_equiv (τ.restrictScalars ℚ_[l]) z).symm

end GlobalTheory
