import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.IsUOfIsUnit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.CrystallineSemistableComparison
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.CharZeroBdR

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge Formalism.Per6 DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

def EtSideS : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  EtSide (Model.Sm (l := l) (K := K))

theorem cstSmooth_of_etSide (gL : GlueL) (gE : GlueE) (gB : GlueB) (hC : BcrisPeriodFacts) (hX : ResEx)
    (hI : EtSideS) (h : Chapters) : CstSmooth := by
  have hS : SeamS := by
    intro l _ K _
    obtain ⟨Amp, h1, h2, h3, h4⟩ := h.p l K
    obtain ⟨β, β₁, e⟩ := gB l K Amp (h.main l) (h.compat l) (h.c1 l)
    obtain ⟨r⟩ := hX l K
    obtain ⟨F⟩ := h4 r
    refine ⟨dat Amp, ⟨gL l K Amp (h.compatH l) (h.rin l) h.uniq h1 h2, gE l K Amp (h.et l K), ⟨β⟩, h3⟩, ?_⟩
    rw [← e] at F
    have := fac l K _ _ _ _ _ β β₁ F
    rwa [(hC l K r).2] at this
  refine ⟨?_, ?_, ?_⟩
  · intro l _ K _ M hM hs n a b
    obtain ⟨D, ⟨hL, ⟨e⟩, ⟨β⟩, ⟨κ⟩⟩, hsp⟩ := hS l K
    obtain ⟨P, hP⟩ := pre l K _ _ D (facts l K) (hI l K) hL e β κ
    exact adm l K _ _ P _ (regCr l K) M ⟨hM, hs⟩ n (inj l K _ _ P (facts l K) (hI l K) M ⟨hM, hs⟩ n).1
      (hP _ _ (t_inv_mem l) (regCr l K).q_mem hsp M ⟨hM, hs⟩ ⟨hM, hs⟩ n) a b
  · intro l _ K _
    obtain ⟨D, ⟨hL, ⟨e⟩, ⟨β⟩, ⟨κ⟩⟩, -⟩ := hS l K
    obtain ⟨P, -⟩ := pre l K _ _ D (facts l K) (hI l K) hL e β κ
    exact ⟨P.cmp (hI l K) (inj l K _ _ P (facts l K) (hI l K))⟩
  · intro l _ K _ r
    obtain ⟨Amp, h1, h2, ⟨κ⟩, h4⟩ := h.p l K
    obtain ⟨β, β₁, e⟩ := gB l K Amp (h.main l) (h.compat l) (h.c1 l)
    obtain ⟨F⟩ := h4 r
    obtain ⟨ε⟩ := gE l K Amp (h.et l K)
    rw [← e] at F
    exact phi l K _ _ _ _ _ (facts l K) (hC l K r).1 (hI l K) (gL l K Amp (h.compatH l) (h.rin l) h.uniq h1 h2) ε β β₁ κ F

end CrystallineSemistableComparison
