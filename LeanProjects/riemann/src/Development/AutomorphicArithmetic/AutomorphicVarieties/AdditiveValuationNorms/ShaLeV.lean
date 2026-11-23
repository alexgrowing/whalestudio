import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Formula

open UpperTheory.V UpperTheory.V.PropA Formalism.GaloisCohomology

theorem UpperTheory.V.PropA.shaLeV :
    GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK →
      ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime],
        PTCase F l → ∀ (D : LData F Ω l) (e : ℤ), shaLen D e ≤ VLen D e := by
  intro hPT hLF hLT F Ω _ _ _ _ _ l _ hc D e
  have hfl := fun r hr => GlobalTheory.TateLimit.finite_level D e hPT hc r hr
  have hsa : PTShaAt D e := GlobalTheory.TateLimit.ptShaAt D e hLF hLT (fun r hr => (hfl r hr).1)
    (fun r hr => (hfl r hr).2.1) (hfl 1 one_pos).2.2
  rw [VLen, ← hsa hc]
  exact Module.length_le_of_injective (f := (Sha2Zl D e).subtype) (hf := Subtype.val_injective)
