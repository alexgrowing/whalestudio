import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeMapComapOfLeConjMaximalCmData
import Formalism.LocalRingCardinality.DataSpaces
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_map_comap_of_le_conj_maximal_cmData : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (P Q : Ideal (𝓞 E)), Q.IsMaximal → P ≤ Q → P ≤ Q.comap (RingOfIntegers.mapRingHom (starRingEnd E)) → P ≤ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
  first | exact @GlobalTheory.UnramifiedConj.le_map_comap_of_le_conj | exact GlobalTheory.UnramifiedConj.le_map_comap_of_le_conj | (intros; apply GlobalTheory.UnramifiedConj.le_map_comap_of_le_conj <;> assumption)
