import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowerZeroEqQ

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.CrC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    (levB : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(W.N T) →+ (ℤ → T.V ⊗[Qp] B))

variable [IsDomain O] [NeZero n] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]

theorem level_zero_membership_of_horizontal (C : Formalism.MainNotions.UnusedSlot80.LevC.Ctx W) (Ti : Formalism.MainNotions.UnusedSlot80.LevE.Comparison₂ W levB)
    (E1 : Formalism.MainNotions.UnusedSlot80.LevE.ExpFrame0 W levB) (E2 : Formalism.MainNotions.UnusedSlot80.LevE.ExpNoNeg0 W levB)
    (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W) (hζex : ∃ ζ : LL, IsPrimitiveRoot ζ PD.p) (A : ArcP n) (hA : A.OK)
    (c' : ZMod n) (hc' : c' ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (e : ℕ) :
    Formalism.MainNotions.UnusedSlot80.LevC.LevelZeroModP (W := W) A c' e T b sol := by
  intro x k f _ hr hfr hx
  obtain ⟨ζ, hζ⟩ := hζex
  choose u hu hfu using hfr
  exact Formalism.MainNotions.UnusedSlot80.CrD.secIn_of_fil W C A hA c' hc' T hT b hb.1 e ζ hζ f u hu hfu
    (fil_of_rep W levB C Ti E1 E2 h4 A hA c' hc' T hT b sol hb e ζ hζ x k f u hfu hr hx)

end Formalism.MainNotions.UnusedSlot80.CrC
