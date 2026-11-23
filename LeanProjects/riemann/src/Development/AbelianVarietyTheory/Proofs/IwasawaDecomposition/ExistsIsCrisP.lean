import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfKernelPowerClosed
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.CrisMap

variable (l : ℕ) [Fact l.Prime]

noncomputable def gA (n : ℕ) : Per.Ainf l →+* Per.AinfP l ⧸ Per.kerP l ^ n :=
  (Ideal.Quotient.mk _).comp (algebraMap (Per.Ainf l) (Per.AinfP l))

noncomputable def fD (n : ℕ) : Per.Acris0 l →+* Per.AinfP l ⧸ Per.kerP l ^ n :=
  (Ideal.Quotient.mk _).comp (Per.Acris0 l).val.toRingHom

theorem unit_l (n : ℕ) : IsUnit ((l : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) := by
  have h : IsUnit (algebraMap (Per.Ainf l) (Per.AinfP l) (l : Per.Ainf l)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have h2 := h.map (Ideal.Quotient.mk (Per.kerP l ^ n))
  rwa [map_natCast, map_natCast] at h2

end GlobalTheory.MemLoc.CrisMap
