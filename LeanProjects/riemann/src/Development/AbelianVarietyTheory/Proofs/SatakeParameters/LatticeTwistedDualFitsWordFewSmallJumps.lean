import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentatStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CrystallineHodgeTateMultiplicityNeZeroOfJumpStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingRestrictsToWachLetterUnramiStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsMemWindowBoxStatement
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem fits_lowCount_of_matRep : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → K.1 ≤ MaximalUnramifiedExtension l → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsMatRep T M' → Fits W T (recWord L j ε g) ∧ ∀ (_ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) (a), lowCount W T a (recWord L j ε g).η ≤ ((recWord L j ε g).m : ℤ) := by
  intro D L C j ε l _ P K LL W c κ ι k r Ms M' g hR hF hK hJ hRd T hT
  obtain ⟨hcr, hmu⟩ := GlobalTheory.T.isCrystalline_jumps_of_isIsoMatrixGaloisRepresentation P K LL T M' hT
  have hmem : ∀ a τ, Over W τ a → ∀ u, IsJumpV (P.PD K) T.ρ τ u →
      u ∈ (recWord L j ε g).win a ∧
        u ∈ Set.Icc (-((recWord L j ε g).Mi a : ℤ)) ((recWord L j ε g).hi a : ℤ) := by
    intro a τ hτ u hu
    have h0 := GlobalTheory.T.crystalline_hodgeTateMultiplicity_ne_zero_of_jump P K LL T hF τ u hu
    rw [hmu, hJ.mult' τ (g a) (hRd τ a hτ) u] at h0
    have hc : u ∈ jT2 (hcAt D (g a)) j (pos ε (g a)) := by
      by_contra hn
      exact h0 (by simp [Multiset.count_eq_zero.mpr hn])
    obtain ⟨h1, h2, _⟩ := GlobalTheory.T.twistedDualJumps_mem_window_box L C j ε g hR a
    exact h1 u (h2 u hc)
  refine ⟨⟨hcr hJ.crys', fun a τ hτ u hu => (hmem a τ hτ u hu).1,
    fun a τ hτ u hu => (hmem a τ hτ u hu).2⟩, ?_⟩
  intro _ft a
  obtain ⟨τ0, hτ0, huniq⟩ := GlobalTheory.T.existsUnique_embeddingRestrictsToWachLetter_unramified P K LL W hK a
  unfold lowCount
  rw [Finset.sum_eq_single_of_mem τ0 (by simpa using hτ0) (fun b hb hne => by
    exact absurd (huniq b (by simpa using hb)) hne)]
  have h3 := (GlobalTheory.T.twistedDualJumps_mem_window_box L C j ε g hR a).2.2
  have he : ∀ u, multV (P.PD K) T.ρ τ0 u = (((jT2 (hcAt D (g a)) j (pos ε (g a))).count u : ℕ) : ℤ) := fun u => by
    rw [hmu, hJ.mult' τ0 (g a) (hRd τ0 a hτ0) u]
  simp only [he]
  exact h3

end GlobalTheory.HTW.Rec
