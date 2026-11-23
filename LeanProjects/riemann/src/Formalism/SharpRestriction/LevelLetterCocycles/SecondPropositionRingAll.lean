import Formalism.SharpRestriction.LevelLetterCocycles.SecondRankCount

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

open Classical in

def SecondPropositionRingInput (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) : Prop :=
  IsUnit (algebraMap (LetA O n) W.EE π') ∧ IsUnit (algebraMap (LetA O n) W.EE Eπ) ∧
  (∃ g ∈ W.AΔ, W.γA W.gamK π' = π' * g) ∧
  ∃ ν ∈ W.AΔ, ν * W.γA W.gamK (Eπ ^ h') = Eπ ^ h' ∧
  ∃ (N : ℕ) (f : ℕ → LetA O n) (cc : ℕ → O),
    (∀ k, f k ∈ W.AΔ) ∧
    (letE c : LetA O n) * ∏ k ∈ Finset.range N, f k = (letE c : LetA O n) * (π' * Eπ ^ (2 * h')) ∧
    (∀ k < N, ∀ a ∈ W.AΔ, ∃ (a₀ : O) (b : LetA O n), b ∈ W.AΔ ∧
      (letE c : LetA O n) * a = (letE c : LetA O n) * (algebraMap O (LetA O n) a₀ + f k * b)) ∧
    (∀ k < N, ∀ a ∈ W.AΔ, ∃ b ∈ W.AΔ,
      (letE c : LetA O n) * (ν * W.γA W.gamK ((∏ j ∈ Finset.range k, f j) * a) -
          algebraMap O (LetA O n) (cc k) * ((∏ j ∈ Finset.range k, f j) * a)) =
        (letE c : LetA O n) * ((∏ j ∈ Finset.range (k + 1), f j) * b)) ∧
    ((Finset.range N).filter fun k => cc k = 1).card ≤ finrank K₀ K + 1

end Local

def secondPropositionRingAll (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ h' : ℕ, 1 ≤ h' → ∀ c, SecondPropositionRingInput ((HW l).W K 1 LL hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c

def SecondRingHypothesis : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → secondPropositionRingAll D HW

end Formalism.MainNotions.N.Ln34

end
