import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisationsAgreeAtLevel

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqLevel

open TopologicalSpace

variable {X : Scheme.{0}}

abbrev sqLB (L : LB X) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)

theorem mem_sq {L : LB X} {x : X} {J : Fin 1 → L.ι} : x ∈ (sqLB L).U J ↔ x ∈ L.U (J 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem mem_sq_pull {Y : Scheme.{0}} {L : LB X} {F : Y ⟶ X} {y : Y} {J : PUnit → Fin 1 → L.ι} :
    y ∈ ((sqLB L).pull F).U J ↔ F y ∈ L.U (J PUnit.unit 0) :=
  mem_pull.trans mem_sq

theorem gm_sq_g {Y : Scheme.{0}} (L : LB X) (r : Y ⟶ X) (y : Y) (J J' : Fin 1 → L.ι) (hJ : r y ∈ L.U (J 0))
    (hJ' : r y ∈ L.U (J' 0)) :
    gm r y ((sqLB L).U J ⊓ (sqLB L).U J') ((sqLB L).g J J') = gm r y _ (L.g (J 0) (J' 0)) ^ 2 := by
  refine (gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => 2) r y J J' (mem_sq.2 hJ) (mem_sq.2 hJ')).trans ?_
  rw [Fin.prod_univ_one, Category.comp_id]
  exact zpow_two _ |>.trans (pow_two _).symm

theorem gm_sq_pull_g {Y Z : Scheme.{0}} (L : LB X) (F : Y ⟶ X) (r : Z ⟶ Y) (z : Z) (J J' : PUnit → Fin 1 → L.ι)
    (hJ : F (r z) ∈ L.U (J PUnit.unit 0)) (hJ' : F (r z) ∈ L.U (J' PUnit.unit 0)) :
    gm r z (((sqLB L).pull F).U J ⊓ ((sqLB L).pull F).U J') (((sqLB L).pull F).g J J') =
      gm (r ≫ F) z _ (L.g (J PUnit.unit 0) (J' PUnit.unit 0)) ^ 2 :=
  (gm_pull_g (sqLB L) F r z J J' (mem_sq_pull.2 hJ) (mem_sq_pull.2 hJ')).trans
    (gm_sq_g L (r ≫ F) z _ _ hJ hJ')

variable {B G E : Scheme.{0}} {M : LB B} {L : LB G} {p : E ⟶ B} {f : E ⟶ G}

theorem sqIso_le (q : (PUnit → Fin 1 → M.ι) × (PUnit → Fin 1 → L.ι)) :
    ((sqLB M).pull p).U q.1 ⊓ ((sqLB L).pull f).U q.2 ≤
      (M.pull p).U (fun _ => q.1 PUnit.unit 0) ⊓ (L.pull f).U (fun _ => q.2 PUnit.unit 0) :=
  fun _ h => ⟨mem_pull.2 (mem_sq_pull.1 h.1), mem_pull.2 (mem_sq_pull.1 h.2)⟩

def sqIso (w : LB.Iso (L.pull f) (M.pull p)) : LB.Iso ((sqLB L).pull f) ((sqLB M).pull p) :=
  ⟨fun q => res (sqIso_le q) (w.s (fun _ => q.1 PUnit.unit 0, fun _ => q.2 PUnit.unit 0)) ^ 2⟩

theorem gw_sqIso (w : LB.Iso (L.pull f) (M.pull p)) {Z : Scheme.{0}} (r : Z ⟶ E) (z : Z) (J : Fin 1 → M.ι)
    (K : PUnit → Fin 1 → L.ι) (hJ : p (r z) ∈ M.U (J 0)) (hK : f (r z) ∈ L.U (K PUnit.unit 0)) :
    gw (sqIso w) r z J K = gw w r z (J 0) (fun _ => K PUnit.unit 0) ^ 2 := by
  have hm : r z ∈ ((sqLB M).pull p).U (fun _ => J) ⊓ ((sqLB L).pull f).U K :=
    ⟨mem_sq_pull.2 hJ, mem_sq_pull.2 hK⟩
  exact (map_pow _ _ _).trans (congrArg (· ^ 2) (gm_res r z _ hm _))

theorem sqIso_isGen {w : LB.Iso (L.pull f) (M.pull p)} (hw : w.IsGen) : (sqIso w).IsGen := by
  rw [isGen_iff] at hw ⊢
  intro Y r y j j' k k' hj hj' hk hk'
  have hj₀ := mem_sq.1 hj
  have hj₀' := mem_sq.1 hj'
  have hk₀ := mem_sq_pull.1 hk
  have hk₀' := mem_sq_pull.1 hk'
  rw [gw_sqIso w r y j k hj₀ hk₀, gw_sqIso w r y j' k' hj₀' hk₀', gm_sq_g M (r ≫ p) y j j' hj₀ hj₀',
    gm_sq_pull_g L f r y k k' hk₀ hk₀']
  have e := hw Y r y (j 0) (j' 0) (fun _ => k PUnit.unit 0) (fun _ => k' PUnit.unit 0) hj₀ hj₀'
    (mem_pull.2 hk₀) (mem_pull.2 hk₀')
  rw [gm_pull_g L f r y _ _ (mem_pull.2 hk₀) (mem_pull.2 hk₀')] at e
  rw [e, mul_pow, mul_pow, inv_pow]

end GlobalTheory.SqLevel
