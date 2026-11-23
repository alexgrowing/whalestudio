import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LevelRestrictionOfGroupLawAlt
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CoefWfZero

namespace Formalism.MainNotions.Ext.CutA

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.GL3r7 Formalism.MainNotions.Ext

theorem firstKernelRemainder_of_levelRestriction_of_linPtW (HK : LevelRestrictionOfGroupLaw) (HL : LinPtW) (D : D7) : StatementFirstKernelRemainder D := by
  intro hph ha he hSD hPD p _ cc δ g hA h5 hI hW κ ι ι' _ _ _ b b' b'' hb hb' hb'' hd ho1 ho2
  have hOk : g.Ok := hA.2.2.2.2
  have hP : CoefWf g.ph := hph p cc δ g hA h5 hI hW
  have hF := (ha p cc δ g hA).2 hW
  have hmem : ∀ (e : (ι ⊕ ι) ⊕ ι') (k : κ), Sum.elim (Sum.elim b b') b'' e k ∈ OKp D g.lam := by
    rintro ((e | e) | e) k
    · exact hb e k
    · exact hb' e k
    · exact hb'' e k
  refine ⟨?_, ?_⟩
  · exact coefWf_sum _ _ fun k _ => coefWf_phAt g hP
      (HL p g hOk hF _ _ (fun e => he p cc δ g hA h5 hI hW _ (hmem e k)) _ _ fun e => ptW_X e)
  · exact HK p g (OKp D g.lam) hOk
      (fun κ ι ι' _ _ _ a a' h1 h2 => (hSD p cc δ g hA h5 hI hW κ ι ι' a a' h1 h2).2.1)
      (fun κ ι _ _ c c' h1 h2 h3 => (hPD p cc δ g hA h5 hI hW κ ι c c' h1 h2 h3).2)
      κ ι ι' b b' b'' hb hb' hb'' hd ho1 ho2

end Formalism.MainNotions.Ext.CutA
