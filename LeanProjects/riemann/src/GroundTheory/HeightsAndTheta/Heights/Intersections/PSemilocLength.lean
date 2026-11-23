import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocLengthSum
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreDivSupp
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerBis
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem SemilocLength.proof (h₁ : SemilocLengthSum.Statement) (h₂ : FibreDivSupp.Statement)
    (h₃ : regularityDehomogenization_holds.Statement) : SemilocLength.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s t α W E hv hP' y hPn hs ht hsP hW htW hy hE
  have := hP'.2.1.1
  have hfib := h₂ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW
  obtain ⟨-, N, hN, hsum⟩ := h₁ K ι K' ι' κ v P' n s t α W E hv hP' y hPn hs ht hsP hW htW hy
    (fun W' hW' hsW' => hE W' ((hfib W').1 ⟨hW', hsW'⟩).1 ((hfib W').1 ⟨hW', hsW'⟩).2)
  refine ⟨N, hN, hsum.trans (finsum_mem_congr (Set.ext fun W' => hfib W') fun W' hW' => ?_)⟩
  obtain ⟨hW'd, hW'i⟩ := hW'
  have hs' : rename v s ∉ P' := hsP
  have ht' : rename v t ∉ W' := fun h => htW (hW'i ▸ h)
  have hy' : fracMapZ v P' y * algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))
      (Ideal.Quotient.mk P' (rename v t)) =
      algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' (rename v s)) := by
    rw [← fracMapZ_algebraMap, ← fracMapZ_algebraMap, ← map_mul, hy]
  rw [(h₃ K' ι' P' (rename v s) (rename v t) (Function.extend κ α 0) W' (fracMapZ v P' y) hP'.2.1
    (rename_isMultiHomog hv hs) hs' hW'd (rename_isMultiHomog hv ht) ht' hy').2]

end GroundTheory.Heights₂.Heights.Inter
