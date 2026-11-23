import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionRingInput
import Formalism.SharpRestriction.LevelLetterCocycles.ModelKStep

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def SecondRankCount (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) : Prop :=
  ∀ S : Submodule O (LcQ W T π' c),
    finrank O (IIrest W T Pt π' Eπ h' c S) ≤ (finrank K₀ K + 1) * finrank O S

end Local

def SecondRankCountAll (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ →
      (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      ∀ c, SecondRankCount ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c

def SecondRankHypothesis : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelLR D HW → SecondRankCountAll D HW

def SecondPropositionOfRank : Prop := ∀ (D : D7) (HW : HWOf D.loc), modelQR D HW → SecondRankCountAll D HW → u2R D HW

theorem second_proposition_of_models (hL : SecondPropositionOfRank) (hQ : ModelQStep) (hR : SecondRankHypothesis) (hML : ModelLStep) : SecondPropositionHypothesis :=
  fun D HW F Cm CA CB CK hA =>
    hL D HW (hQ D HW F Cm CA CB CK hA) (hR D HW F Cm CA CB CK hA (hML D HW F Cm CA CB CK hA))

end Formalism.MainNotions.N.Ln34

end
