import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdmissibleOfCongrUnitriangular
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_admissible_of_congr_unitriangular : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : HSpace E} {r : ℕ} (Λ : Submodule (𝓞 E) S.V) (g : ℕ), g ≠ 0 → ∀ {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → M a b = 0) → (∀ a, M a a = 1) → (∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a b, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * M a b = o) → (∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a, frame F a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) → (∀ b, ModG S Λ g (frame F' b - ∑ a, M a b • frame F a)) → IsAdmissible Λ g F F' := by
  first | exact @GlobalTheory.admissible_of_congr_unitriangular | exact GlobalTheory.admissible_of_congr_unitriangular | (intros; apply GlobalTheory.admissible_of_congr_unitriangular <;> assumption)
