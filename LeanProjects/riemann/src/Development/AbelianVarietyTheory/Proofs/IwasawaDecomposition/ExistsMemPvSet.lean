import Mathlib
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderSmulOfFix
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.PlaceOverPair

theorem exists_mem_pvSet {R : Ranks} (H : Formalism.BasicNotions.Host R) {p : ℕ} (hp : p.Prime) (𝔭 : HeightOneSpectrum (𝓞 H.K))
    (h𝔭 : (p : 𝓞 H.K) ∈ 𝔭.asIdeal) (v : HeightOneSpectrum (𝓞 H.F)) (hv : OverPF H p v) : ∃ w, w ∈ PvSet H 𝔭 v := by
  obtain ⟨w, h1, h2⟩ := exists_over_both H hp 𝔭 h𝔭 v hv
  refine ⟨w, ?_, h2⟩
  rw [aboveF, Set.Finite.mem_toFinset]
  exact h1

theorem exists_places : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (𝔭 𝔭' : HeightOneSpectrum (𝓞 H.K)),
    ((H.pde : ℕ) : 𝓞 H.K) ∈ 𝔭.asIdeal → ((H.pde' : ℕ) : 𝓞 H.K) ∈ 𝔭'.asIdeal →
      ∃ B : PlacesOverCommonPrime H, B.pK = 𝔭 ∧ B.pK' = 𝔭' := by
  intro R H 𝔭 𝔭' h h'
  choose P hP using exists_mem_pvSet H H.pde_prime 𝔭 h
  choose P' hP' using exists_mem_pvSet H H.pde'_prime 𝔭' h'
  exact ⟨⟨𝔭, 𝔭', h, h', P, P', hP, hP'⟩, rfl, rfl⟩

end GlobalTheory.PlaceOverPair
