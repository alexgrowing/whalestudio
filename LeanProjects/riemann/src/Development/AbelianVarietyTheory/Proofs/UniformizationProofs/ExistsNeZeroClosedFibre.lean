import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEquivOfIsPushout
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZeroOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpreadSec

variable {X X' : Scheme.{0}}

theorem exists_pull {M : LB X} (s : LB.Sec M) (π : X' ⟶ X) :
    ∃ t : LB.Sec (M.pull π), ∀ (j : (M.pull π).ι) (z : X'), π z ∈ M.U (j PUnit.unit) →
      gs (𝟙 X') z _ (t.f j) = gs π z _ (s.f (j PUnit.unit)) := by
  let a : ∀ j : (M.pull π).ι, Γ(X', (M.pull π).U j) := fun j =>
    rs X' (LB.wchart_le M (fun _ : PUnit => π) j PUnit.unit) ((π.app _).hom (s.f (j PUnit.unit)))
  have ha : ∀ (j : (M.pull π).ι) (z : X'), π z ∈ M.U (j PUnit.unit) →
      gs (𝟙 X') z _ (a j) = gs π z _ (s.f (j PUnit.unit)) := fun j z hz => by
    have hm : (𝟙 X' : X' ⟶ X') z ∈ (M.pull π).U j := Set.mem_iInter.2 fun _ => hz
    refine (gs_res (𝟙 X') z _ hm _).trans ?_
    rw [gs_pull (𝟙 X') π z _ hz, Category.id_comp]
  refine ⟨⟨a, fun i j => fn_ext fun z hz => ?_⟩, ha⟩
  have hi : π z ∈ M.U (i PUnit.unit) := Set.mem_iInter.1 hz.1 PUnit.unit
  have hj : π z ∈ M.U (j PUnit.unit) := Set.mem_iInter.1 hz.2 PUnit.unit
  refine ((gs_res (𝟙 X') z _ hz _).trans (ha i z hi)).trans (Eq.trans ?_ ((gs_mul (𝟙 X') z _ hz _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 X') z _ hz _).trans
      (congrArg Units.val (gm_linComb M _ _ (𝟙 X') z i j hz.1 hz.2))) ((gs_res (𝟙 X') z _ hz _).trans
        (ha j z hj)))).symm)
  rw [FlatSec.gs_sec_trans s π z hi hj, Fintype.prod_unique, zpow_one, Category.id_comp]

theorem app_eq_zero {M : LB X} {π : X' ⟶ X} (h : ∀ (t : LB.Sec (M.pull π)) j, t.f j = 0) (s : LB.Sec M) (k : M.ι) :
    (π.app _).hom (s.f k) = 0 := by
  obtain ⟨t, ht⟩ := exists_pull s π
  refine fn_ext fun z hz => ?_
  have hz' : π z ∈ M.U k := hz
  rw [gs_pull (𝟙 X') π z _ hz', Category.id_comp, ← ht (fun _ => k) z hz',
    LBGerm.gs_zero (𝟙 X') z _ hz]
  refine (congrArg (gs (𝟙 X') z _) (h t fun _ => k)).trans ?_
  exact LBGerm.gs_zero (𝟙 X') z _ (Set.mem_iInter.2 fun _ => hz')

theorem exists_ne_zero_closed_fibre : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom] (N : LB G.left), N.IsLB → (∃ s : LB.Sec (N.pull (pullback.fst G.hom (jK V))), (∃ j, s.f j ≠ 0)) → ∃ s : LB.Sec (N.pull (fstG (IsLocalRing.maximalIdeal V) 0 G).left), (∃ j, s.f j ≠ 0) := by
  intro V _ _ _ G _ _ _ _ _ N hN ⟨s, j, hj⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have h0 : ∀ σ : LB.Sec N, ∃ τ : LB.Sec N, DVR.SecIsMul G.hom (ϖ ^ (0 + 1)) σ τ := fun σ =>
    (ThickDiv.main V ϖ hϖ G N σ 0).1 (app_eq_zero hcon σ)
  have h1 : ∀ (n : ℕ) (σ : LB.Sec N), ∃ τ : LB.Sec N, DVR.SecIsMul G.hom (ϖ ^ (n + 1)) σ τ := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      intro σ
      obtain ⟨τ, hτ⟩ := ih σ
      obtain ⟨ρ, hρ⟩ := h0 τ
      refine ⟨ρ, fun k => ?_⟩
      have e₁ : σ.f k = AbLaw.cst G.hom _ (ϖ ^ (n + 1)) * τ.f k := hτ k
      have e₂ : τ.f k = AbLaw.cst G.hom _ (ϖ ^ (0 + 1)) * ρ.f k := hρ k
      change σ.f k = AbLaw.cst G.hom _ (ϖ ^ (n + 1 + 1)) * ρ.f k
      rw [e₁, e₂, ← _root_.mul_assoc, ← map_mul, ← pow_add]
  have h2 : ∀ (σ : LB.Sec N) k, σ.f k = 0 := fun σ =>
    (sec_eq_zero_and_hom_eq_of_thickenings V (IsLocalRing.maximalIdeal V)
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge G).1 N hN σ fun n =>
        (ThickDiv.main V ϖ hϖ G N σ n).2 (h1 n σ)
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat V (FractionRing V) (algebraMap V _)
    (RingHom.flat_algebraMap_iff.2 inferInstance) G.left G.hom _ _ _
    (IsPullback.of_hasPullback G.hom (jK V)) N hN s
  refine hj (fn_ext fun z hz => ?_)
  have hz' : pullback.fst G.hom (jK V) z ∈ N.U (j PUnit.unit) := Set.mem_iInter.1 hz PUnit.unit
  rw [LBGerm.gs_zero _ z _ hz]
  refine (hu z (j PUnit.unit) hz').trans (Finset.sum_eq_zero fun i _ => ?_)
  rw [h2, LBGerm.gs_zero _ z _ hz', mul_zero]

end GlobalTheory.SpreadSec
