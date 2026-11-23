import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplexStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionNeZero
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ

theorem codiscreteWithin_Hs_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have hmem : (∅ : Set ℂ) ∈ Filter.codiscreteWithin Hs := by rw [h]; exact Filter.mem_bot
  rw [mem_codiscreteWithin] at hmem
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hd := hmem Complex.I hI
  simp only [Set.diff_empty] at hd
  have hopen : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have hle : nhdsWithin Complex.I {Complex.I}ᶜ ≤ Filter.principal Hs :=
    le_trans nhdsWithin_le_nhds (Filter.le_principal_iff.2 (hopen.mem_nhds hI))
  have hbot : nhdsWithin Complex.I {Complex.I}ᶜ = ⊥ := by
    have := hd.mono_right hle
    exact disjoint_self.1 this
  exact (NormedField.nhdsNE_neBot Complex.I).ne hbot

theorem siegel_ne_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (x : Fin 2 → ℚ), admitted c x → siegel T c x ≠ 0 := by
  intro Ω _ _ _ ε T c x hx h0
  have han := GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hx
  rw [h0, map_zero] at han
  have hev : (fun z => sgC c x z) =ᶠ[Filter.codiscreteWithin Hs] (fun _ => (0 : ℂ)) :=
    (Filter.Germ.coe_eq.1 han.symm)
  have hne : ∀ᶠ z in Filter.codiscreteWithin Hs, sgC c x z ≠ 0 := by
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
    have hz' : 0 < z.im := hz
    simp only [sgC, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
    exact sg_ne_zero c x _ hx
  haveI := codiscreteWithin_Hs_neBot
  obtain ⟨z, h1, h2⟩ := (hev.and hne).exists
  exact h2 h1

end GlobalTheory.KZ
