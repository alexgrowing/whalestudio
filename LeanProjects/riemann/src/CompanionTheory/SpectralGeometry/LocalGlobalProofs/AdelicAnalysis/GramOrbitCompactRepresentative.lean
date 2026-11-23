import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalGramAdelicCompactFiniteStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompactPartClosedOrbit
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionRationalToAdelicStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Proper

theorem compact_gram_fibre :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      ∀ (n : ℕ) (X : Fin n → Fin M → E), (gramE σ J X).det ≠ 0 →
      ∀ Ω : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact Ω →
      ∃ C : Set (HA (AF F) σ J), IsCompact C ∧
        ∀ Y ∈ Ω, gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) →
          ∃ c ∈ C, actW (AF F) σ J c (ratTup (AF F) X) = Y := by
  intro F E _ _ _ _ _ σ hσ M J hJ n X hX Ω hΩ
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hlc
  haveI := hsc
  haveI := ht2
  obtain ⟨htg, hlcH, hscH, ht2H, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  haveI := htg
  haveI := hlcH
  haveI := hscH
  haveI := ht2H
  obtain ⟨-, hlcK, -, ht2K, -, -, -, -, -, hgram⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)
  haveI := hlcK
  haveI := ht2K
  obtain ⟨hcont, h1, hmul, hinv⟩ := hact n
  obtain ⟨-, hrat, -⟩ := GlobalTheory.T.rational_gram_adelic_compact_finite F E σ hσ M J hJ
  have hZ : IsClosed {Y : Fin n → Fin M → AF F ⊗[F] E |
      gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F))} :=
    isClosed_eq (hgram n M J) continuous_const
  have hZx : ∀ Y : Fin n → Fin M → AF F ⊗[F] E,
      Y ∈ {Y : Fin n → Fin M → AF F ⊗[F] E |
        gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F))} ↔
      ∃ g : HA (AF F) σ J, actW (AF F) σ J g (ratTup (AF F) X) = Y := by
    intro Y
    constructor
    · intro hY
      exact GlobalTheory.T.witt_extension_rational_to_adelic F E σ hσ M J hJ n X Y hX hY
    · rintro ⟨g, rfl⟩
      show gramR (AF F) σ J _ = _
      rw [hinv, hrat]
  obtain ⟨C, hC, hCY⟩ := GlobalTheory.CompanionTheory.Adelic.compact_part_closed_orbit (HA (AF F) σ J)
    (Fin n → Fin M → AF F ⊗[F] E) (fun g Y => actW (AF F) σ J g Y) hcont h1 hmul _
    (ratTup (AF F) X) hZ hZx Ω hΩ
  exact ⟨C, hC, fun Y hY hg => hCY Y hY hg⟩

end GlobalTheory.CompanionTheory.SW.Proper
