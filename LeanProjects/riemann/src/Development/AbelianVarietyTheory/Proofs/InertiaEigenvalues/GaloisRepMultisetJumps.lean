import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.GalSum

theorem inducesW_unique {D : D7} {i : D.nd.Loc} {τ : D.host.E →+* Qbar (D.nd.l i)} {w w' : PlE D.host}
    (h : InducesW D.nd i τ w) (h' : InducesW D.nd i τ w') : w' = w := by
  apply HeightOneSpectrum.ext
  ext x
  rw [← h x, h' x]

theorem main : ∀ D : D7, SumRepresentations.tie0 D → ∀ (i : D.nd.Loc) (a b : ℕ) (ρ : GE D.nd →* GL (Fin a) (Qbar (D.nd.l i))) (ρ' : GE D.nd →* GL (Fin b) (Qbar (D.nd.l i))) (p q : ∀ w, D.naut.LP w) (m m' : (D.host.E →+* ℂ) → Multiset ℂ), (SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧ (∀ w, D.naut.wdOf i ρ w = p w) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) = m ((D.naut.iotaQC i).toRingHom.comp τ)) → (SumRepresentations.At.ContQ D.nd i ρ' ∧ IsSSRep ρ' ∧ (∀ w, D.naut.wdOf i ρ' w = q w) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ' w ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ' τ).map (fun n : ℤ => (n : ℂ)) = m' ((D.naut.iotaQC i).toRingHom.comp τ)) → ∃ σ : GE D.nd →* GL (Fin (a + b)) (Qbar (D.nd.l i)), (SumRepresentations.At.ContQ D.nd i σ ∧ IsSSRep σ ∧ (∀ w, D.naut.wdOf i σ w = D.naut.lpSum (p w) (q w)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i σ w ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i σ τ).map (fun n : ℤ => (n : ℂ)) = m ((D.naut.iotaQC i).toRingHom.comp τ) + m' ((D.naut.iotaQC i).toRingHom.comp τ)) := by
  intro D hT i a b ρ ρ' p q m m' ⟨c, s, hp, hw⟩ ⟨c', s', hq, hw'⟩
  obtain ⟨-, -, hGal⟩ := hT
  obtain ⟨-, -, hsum, -⟩ := hGal.2.2.2 i
  obtain ⟨hdR, hwd, hj⟩ := hsum a b ρ ρ' c c'
  have wdok : ∀ w, SumRepresentations.At.WDok D.nd D.naut i ρ w ∧ SumRepresentations.At.WDok D.nd D.naut i ρ' w := by
    intro w
    by_cases hl : w ∈ placesOver D.host.E (D.nd.l i)
    · exact ⟨Or.inr (hw w hl).1, Or.inr (hw' w hl).1⟩
    · exact ⟨Or.inl hl, Or.inl hl⟩
  refine ⟨SumRepresentations.At.sumRep ρ ρ', GlobalTheory.BCGal.cont_sumRep ρ ρ' c c', GlobalTheory.BCGal.ss_sumRep ρ ρ' s s', fun w => ?_,
    fun w hl => ⟨(hdR w hl).2 ⟨(hw w hl).1, (hw' w hl).1⟩, fun τ hτ => ?_⟩⟩
  · rw [hwd w (wdok w).1 (wdok w).2, hp, hq]
  · have key : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i ρ w' ∧ D.naut.IsdRW i ρ' w' := by
      intro w' h'
      rw [inducesW_unique hτ h']
      exact ⟨(hw w hl).1, (hw' w hl).1⟩
    rw [hj τ key, Multiset.map_add, (hw w hl).2 τ hτ, (hw' w hl).2 τ hτ]

end GlobalTheory.GalSum
