import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLevelTypePrimeDatumLocallySmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLevel_typePrime_datum_locally_small : ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k rS r t j c' n' c n : ℕ), q ≠ 0 → (q : 𝓞 E) ∈ P.asIdeal → n' + c' = r + (j - 1) * t → n' + c' ≤ n + c → k ≤ n' → k ≤ n → k ≤ r → LocSmall q (LocE.lamY P q n' c' fun i => i + 1) (LocE.lamY P q n c fun i => i + 1) (LocE.PhiGS q ψ χ k rS r t j c' n' c n) 1 := by
  first | exact @GlobalTheory.SymLevelDatum.locSmall_phiGS | exact GlobalTheory.SymLevelDatum.locSmall_phiGS | (intros; apply GlobalTheory.SymLevelDatum.locSmall_phiGS <;> assumption)
