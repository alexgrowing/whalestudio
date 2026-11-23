import Formalism.CharacterColumnKernels.StatementGC
import Formalism.CharacterColumnKernels.IdempotentNormalForms.GlobalModuleOf
import Formalism.CharacterColumnKernels.IdempotentNormalForms.CupKillAdm
import Formalism.CharacterColumnKernels.IdempotentNormalForms.GlobalConcreteOf

open Finset

noncomputable section

namespace Formalism.NG

theorem globalColumn : StatGlobalColumn := by
  intro O _ _ _ X X' T T' Z p q b hspan hinj d _ _ R' _ hdet Tc _ _ _ _ G _ r χ E e₁ δ ι _ _ D j
    Kc k0 hE he₁ hpt g₀ n hn π' ρπ hρπ α _ _ bl hbl ρk hρk hblk _ hcard
  refine globalModule O X X' T T' Z p q b hspan hinj d R' hdet
    (ColNNJ r χ E e₁ δ D j Kc k0) g₀ n hn ?_ π' ρπ hρπ α bl hbl ρk hρk hblk hcard
  intro x' hx'
  obtain ⟨δx, hδx, hδ, hEr, he₁r, hfix, hL⟩ := hpt x' hx'
  exact columnJ R' Tc (FractionRing O) (EvalSp O d R' x') G r χ E e₁ δ ι D j Kc k0 hE he₁
    δx hδx hδ hEr he₁r hfix hL

end Formalism.NG
