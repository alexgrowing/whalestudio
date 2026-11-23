import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FibreCountOfIdentification
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LretrCancel
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LadjFrame
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LFrame

noncomputable section

open scoped Classical Pointwise

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem c3eqv_loc_mono {P : Ideal (𝓞 E)} [P.IsPrime] {L L' : Submodule (𝓞 E) S.V} (h : L ≤ L') :
    Formalism.HermitianLatticesTheory.localization₂ P L ≤ Formalism.HermitianLatticesTheory.localization₂ P L' := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := hx
  exact ⟨s, hs, h hx⟩

theorem c3eqv_le_loc {P : Ideal (𝓞 E)} [hP : P.IsPrime] (L : Submodule (𝓞 E) S.V) : L ≤ Formalism.HermitianLatticesTheory.localization₂ P L := by
  intro x hx
  exact ⟨1, P.primeCompl.one_mem, by rwa [one_smul]⟩

variable {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}

end Gen

section Fin

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

end Fin

end Formalism.MainNotions.BridgeLemma₂

end
