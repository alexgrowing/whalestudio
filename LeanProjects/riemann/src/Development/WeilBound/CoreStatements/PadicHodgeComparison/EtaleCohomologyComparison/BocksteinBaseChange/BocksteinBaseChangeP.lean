import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.StmtPhi
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

def GlueL : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  (Amp : ∀ M : Model l K, E.LineData M.X → Prop), B.CompatH l → E.RIn l → E.FirstChernUniqueEtale → (∀ M D, Amp M D → Etale D.f) →
    (∀ M : Model l K, M.Sm → ∃ D, Amp M D) → (dat Amp).Laws Model.Sm

def GlueE : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  (Amp : ∀ M : Model l K, E.LineData M.X → Prop), E.EtMap l K → Nonempty (EMap Model.Sm (dat Amp))

def GlueB : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  (Amp : ∀ M : Model l K, E.LineData M.X → Prop), B.Main l → B.Compat l → B.FirstChernCompatible l →
    ∃ (β : BMap Model.Sm (dat Amp)) (β₁ : BPhi β), @β₁.pull = @datPull l _ K Amp

def BocksteinBaseChangeP : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  ∃ Amp : ∀ M : Model l K, E.LineData M.X → Prop, (∀ M D, Amp M D → Etale D.f) ∧ (∀ M : Model l K, M.Sm → ∃ D, Amp M D) ∧
    Nonempty (PMap Model.Sm (dat Amp)) ∧ ∀ r : Res l K, Nonempty (FMap Model.Sm r.perC r.iso (dat Amp) (datPull Amp))

end CrystallineSemistableComparison
