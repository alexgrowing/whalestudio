import Formalism.SharpRestriction.LevelLetterCocycles.LevelOneUniformizerCoeffVanish
import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfLevelZeroParts
import Formalism.SharpRestriction.LevelLetterCocycles.StrictSesLetter
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
import Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor
import Formalism.SharpRestriction.LevelLetterCocycles.LevelZeroMembershipOfHorizontal

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.Crit0

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def LevelMapsCompatible (W : LocWach PD LL O v n) (levB : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(W.N T) →+ (ℤ → T.V ⊗[Qp] B))
    [IsDomain O] [NeZero n] : Prop :=
  LevC.Ctx W → LevE.Comparison₂ W levB → LevE.ExpFrame0 W levB → LevE.ExpNoNeg0 W levB → Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W →
    (∃ ζ : LL, IsPrimitiveRoot ζ PD.p) → ∀ A : ArcP n, A.OK → ∀ c' ∈ A.cuts, ∀ T : LocLat G Qp LL O, Win W A T →
      ∀ {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL), IsHor W T c' b sol →
        ∀ e : ℕ, LevC.LevelZeroModP (W := W) A c' e T b sol

end Formalism.MainNotions.UnusedSlot80.Crit0

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

theorem exists_prim_of_good (D : D7) {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (hG : Good K 1 LL) :
    ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l := by
  have hmem : (D.loc l).ζQ 1 ∈ Ks K 1 := by
    apply (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} ≤ Ks K 1)
    apply IntermediateField.subset_adjoin
    show (D.loc l).ζQ 1 ^ (l ^ 1) = 1
    rw [pow_one, (D.loc l).ζQ_succ 0, (D.loc l).ζQ_zero]
  have hLL : (D.loc l).ζQ 1 ∈ LL.1 := hG.2.2.2 (Ks K 1).val ⟨_, hmem⟩
  refine ⟨⟨_, hLL⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) (hf := Subtype.val_injective)
    (LevR.root_of_unity_primitive D l)

theorem lev0MpL_of_from (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hAdm : AdmArcA D HW F Cm) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hW : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), CaseA K LL → 5 ≤ l →
      haveI := neZero_finrank_max_unramified K
      Crit0.LevelMapsCompatible ((HW l).W K 1 LL hG) ((Cm l).C K 1 LL hG).tie.levB) :
    LevelZeroModPLocal D HW := by
  intro l _ K LL hG hCA h5l A hA c' hc' T hT d b sol hb e
  have := neZero_finrank_max_unramified K
  have C := ctx_of D HW F Cm hAdm l K LL hG hCA h5l
  have Ti := levETie_of D HW F Cm h4 l K LL hG
  have E1 := LevE.expFrame0_of Ti C.hs C.hR C.hp0 C.h5 C.hH C.hCA
  have E2 := LevE.expNoNeg0_of Ti C.hs C.hR C.hp0 C.h5
  have h4' := Strict.p4YL D HW F (levCoeff_of_pt D HW F Cm h4 (points_exist_of_ring_condition D HW F h9)) l K LL hG hCA h5l
  obtain ⟨ζ, hζ⟩ := exists_prim_of_good D hG
  have hζ' : ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ ((D.loc l).PD K).p := ⟨ζ, by rw [(D.loc l).PD_p]; exact hζ⟩
  exact hW l K LL hG hCA h5l C Ti E1 E2 h4' hζ' A hA c' hc' T hT b sol hb e

theorem lev0MpL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hAdm : AdmArcA D HW F Cm) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) : LevelZeroModPLocal D HW :=
  lev0MpL_of_from D HW F Cm hAdm h4 h9 fun l _ K LL hG _ _ => by
    haveI := neZero_finrank_max_unramified K
    haveI := eq_sum_herm_smul_frame_of_inW (D.loc l) K LL
    intro C Ti E1 E2 h4' hζ A hA c' hc' T hT d b sol hb e
    exact CrC.level_zero_membership_of_horizontal _ _ C Ti E1 E2 h4' hζ A hA c' hc' T hT b sol hb e

end Formalism.MainNotions.UnusedSlot80
