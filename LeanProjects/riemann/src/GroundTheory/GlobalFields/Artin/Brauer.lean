import Mathlib
import GroundTheory.GlobalFields.Artin.Induction
import GroundTheory.GlobalFields.Artin.OneDimL
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.LocalFields.BrauerInduction
set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain NumberField IntermediateField Filter Topology Set

namespace GroundTheory.Global

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

variable (K L) in
open Classical in

def continuedArtinL (f : Gal(L/K) → ℂ) : ℂ → ℂ :=
  if h : ∃ F : ℂ → ℂ, MeromorphicNFOn F univ ∧ ∀ s : ℂ, 1 < s.re → F s = artinL K L f s then
    h.choose else 0

section Subgroup

variable (H : Subgroup Gal(L/K))

def fixedFieldChar (l : H →* ℂˣ) : Gal(L/fixedField H) →* ℂˣ :=
  l.comp (Artin.fixedFieldMulEquiv H).symm.toMonoidHom

end Subgroup

section Product

variable [Fintype Gal(L/K)] {ι : Type*} [Fintype ι] {H : ι → Subgroup Gal(L/K)} [∀ i, Fintype (H i)]
  (c : ι → ℤ) (l : ∀ i, H i →* ℂˣ)

end Product

section Virtual

variable [Fintype Gal(L/K)]

open GroundTheory.LocalField

end Virtual

end GroundTheory.Global
