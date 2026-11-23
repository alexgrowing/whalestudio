import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsDataDualGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSupercuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalCompGeneralLinearGroupMapOfFieldE
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.InvTransposeCusp

theorem invTranspose_invol {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    GlobalTheory.TypeTame.invTranspose n (GlobalTheory.TypeTame.invTranspose n g) = g := by
  apply Units.ext
  exact Matrix.transpose_transpose (g : Matrix (Fin n) (Fin n) R)

theorem isSupercuspidal_comp_invTranspose (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSupercuspidal π) :
    IsSupercuspidal (π.comp (GlobalTheory.TypeTame.invTranspose n)) := by
  have hcont := GlobalTheory.TypeTame.continuous_invTranspose (R := k) n
  obtain ⟨hsm, hc⟩ := hs
  refine ⟨fun v => (hsm v).preimage hcont, ?_⟩
  intro v l hl
  have hl' : l ∈ smoothPart π.dual := by
    show IsOpen {g | π.dual g l = l}
    have : {g | π.dual g l = l} = (GlobalTheory.TypeTame.invTranspose n) ⁻¹'
        {g | Representation.dual (π.comp (GlobalTheory.TypeTame.invTranspose n)) g l = l} := by
      ext g
      simp [Representation.dual, map_inv, invTranspose_invol]
    rw [this]
    exact hl.preimage hcont
  obtain ⟨C, hC, hCl⟩ := hc v l hl'
  refine ⟨(GlobalTheory.TypeTame.invTranspose n) '' C, hC.image hcont, fun g hg => ?_⟩
  obtain ⟨z, hz, c, hcC, hgc⟩ := hCl (GlobalTheory.TypeTame.invTranspose n g) hg
  refine ⟨GlobalTheory.TypeTame.invTranspose n z, ?_, GlobalTheory.TypeTame.invTranspose n c, ⟨c, hcC, rfl⟩, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro h
    have := Subgroup.mem_center_iff.1 hz (GlobalTheory.TypeTame.invTranspose n h)
    have h2 := congrArg (GlobalTheory.TypeTame.invTranspose n) this
    simpa [map_mul, invTranspose_invol] using h2
  · rw [← map_mul, ← hgc, invTranspose_invol]

theorem isCuspidal_comp_invTranspose : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsCuspidal π → IsCuspidal (π.comp (GlobalTheory.TypeTame.invTranspose n)) := by
  intro k _ _ _ _ n V _ _ π h
  exact GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal k n V _
    (isSupercuspidal_comp_invTranspose k n V π
      (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k n V π h))

end GlobalTheory.InvTransposeCusp
