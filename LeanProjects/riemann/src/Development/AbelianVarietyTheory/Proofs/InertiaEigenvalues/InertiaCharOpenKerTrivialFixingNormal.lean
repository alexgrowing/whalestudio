import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCyclic
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem char_inertia_trivial_on_fixing_normal : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l)
    (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ), IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) →
    ∃ F : FinExt l, Normal ℚ_[l] ↥F.1 ∧ ∀ g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)),
      (∀ x ∈ F.1, ((g : Gl l) : GQ l) x = x) → χ g = 1 := by
  intro l _ LL χ hopen
  obtain ⟨t₁, ht₁, ht₁e⟩ := isOpen_induced_iff.mp hopen
  obtain ⟨t₂, ht₂, ht₂e⟩ := isOpen_induced_iff.mp ht₁
  have h1 : (1 : GQ l) ∈ t₂ := by
    have hk : (1 : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) ∈ (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) := χ.ker.one_mem
    rw [← ht₁e] at hk
    have hk' : ((1 : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) : Gl l) ∈ t₁ := hk
    rw [← ht₂e] at hk'
    exact hk'
  obtain ⟨E, hfd, hN, hE⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ_[l] (Om l) t₂).1 (ht₂.mem_nhds h1)
  refine ⟨⟨E, hfd⟩, hN, fun g hg => ?_⟩
  have hg₂ : ((g : Gl l) : GQ l) ∈ t₂ :=
    hE ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => hg x hx)
  have hg₁ : (g : Gl l) ∈ t₁ := by
    rw [← ht₂e]; exact hg₂
  have hg₀ : g ∈ (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) := by
    rw [← ht₁e]; exact hg₁
  exact hg₀

end GlobalTheory.InertiaEigenvalues
