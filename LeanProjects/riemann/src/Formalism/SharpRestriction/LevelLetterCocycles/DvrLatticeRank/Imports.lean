import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionHypothesis

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def Phi (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) {r : ℕ} (rep : Fin r → W.DD T) :
    (Fin r → LL) →ₗ[LL] T.V ⊗[Qp] BdR where
  toFun d := ∑ k, d k • valAt W T c ζ (rep k)
  map_add' d d' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a d := by simp [Finset.smul_sum, smul_smul]

theorem Phi_apply (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) {r : ℕ} (rep : Fin r → W.DD T)
    (d : Fin r → LL) : Phi W T c ζ rep d = ∑ k, d k • valAt W T c ζ (rep k) := rfl

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
