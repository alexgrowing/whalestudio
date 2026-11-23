import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKoszulCech
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KoszulCech

noncomputable section

def KoszulCechExact.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ) (R : ℕ)
    (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0),
    (∀ I : KH.Cell K ι 0, ∃ u : Fin R → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V),
      (∀ j, u j ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-α)) ∧ ∑ j, u j * z j I = 1) →
    ∀ (c : K → ℤ) (n : ℕ),
      (∀ φ ∈ kosPart S ι V R α c 0 n, ∃ ψ ∈ kosPart S ι V R α c 1 n, kosD z 0 n ψ = φ) ∧
      (∀ p : ℕ, ∀ φ ∈ kosPart S ι V R α c (p + 1) n, kosD z p n φ = 0 →
        ∃ ψ ∈ kosPart S ι V R α c (p + 2) n, kosD z (p + 1) n ψ = φ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
