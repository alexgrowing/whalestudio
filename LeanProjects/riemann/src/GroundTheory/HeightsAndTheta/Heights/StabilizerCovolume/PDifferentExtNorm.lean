import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.RecordEigen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField

theorem absNorm_extDifferent {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L) :
    letI : Algebra E L := ι.toAlgebra
    Ideal.absNorm (extDifferent ι) = (discr E).natAbs ^ Module.finrank E L := by
  let _ : Algebra E L := ι.toAlgebra
  have h1 : RingOfIntegers.mapRingHom ι = algebraMap (𝓞 E) (𝓞 L) := rfl
  have h3 : Module.finrank (𝓞 E) (𝓞 L) = Module.finrank E L :=
    (IsFractionRing.finrank_eq (𝓞 E) E (𝓞 L) L).symm
  rw [extDifferent, h1, Ideal.absNorm_algebraMap, absNorm_differentIdeal E (𝓞 E), h3]

theorem DifferentExtNorm.full : DifferentExtNorm.Statement := by
  intro E L _ _ _ _ ι
  refine ⟨extDifferent_ne_bot ι, ?_⟩
  let _ : Algebra E L := ι.toAlgebra
  have hN := absNorm_extDifferent ι
  have hd : (discr E) ≠ 0 := discr_ne_zero E
  have hE : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have hdeg : Module.finrank ℚ L = Module.finrank ℚ E * Module.finrank E L :=
    (Module.finrank_mul_finrank ℚ E L).symm
  rw [hN, logRd, Nat.cast_pow, Real.log_pow, hdeg, Nat.cast_mul]
  have habs : ((discr E).natAbs : ℝ) = |(discr E : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [habs]
  field_simp

end GroundTheory.Heights₂.Heights.NineStatements
