import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleDescentBijectiveAppStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOffClosedFibreDescendedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorDescendedBundleNearClosedPointStatement

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CubeDesc

theorem app_bijective (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : AdmBase R (maximalIdeal R))
    (M : Modif R) (G' : Over M.S) (G : Over (Sp R)) (β : G'.left ⟶ G.left) (hf : Flat G.hom)
    (hp : IsPullback β G'.hom G.hom M.π) : ∀ V : G.left.Opens, Function.Bijective (β.app V).hom := by
  obtain ⟨hN, -, hI, -⟩ := hR
  haveI := M.proper
  exact GlobalTheory.T.app_bijective_of_flat_baseChange_globalFunctions R M.S G.left G'.left M.π G.hom β G'.hom inferInstance inferInstance
    (GlobalTheory.T.appTop_bijective_and_surjective_normalDomain R M).1 hf hp

theorem exists_closed_spec (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) (hG : QuasiCompact G.hom)
    (y : G.left) (hy : G.hom y = closedPoint R) :
    ∃ z : G.left, IsClosed ({z} : Set G.left) ∧ y ⤳ z ∧ G.hom z = closedPoint R := by
  haveI : CompactSpace G.left := by
    haveI := hG
    exact QuasiCompact.compactSpace_of_compactSpace G.hom
  obtain ⟨z, hz, hzc⟩ := (isClosed_closure (s := ({y} : Set G.left))).exists_closed_singleton ⟨y, subset_closure rfl⟩
  have hyz : y ⤳ z := specializes_iff_mem_closure.2 hz
  refine ⟨z, hzc, hyz, ?_⟩
  have h := hyz.map G.hom.base.hom.continuous
  rw [hy] at h
  have hc : IsClosed ({closedPoint R} : Set (PrimeSpectrum R)) := isClosed_singleton_closedPoint R
  have h' := specializes_iff_mem_closure.1 h
  exact hc.closure_subset h'

theorem cubicalBundle_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ (θ : P'.L.L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ i, g ∈ G'.left.basicOpen (θ.f i)) → ∃ L : LB G.left, L.IsLB ∧ LBIso P'.L.L (L.pull β) := by
  intro R _ _ _ hR M G' _ _ hG' P' G _ _ β hG hpb θ O hO hθ
  have hflat : Flat G.hom := by haveI := hG.smooth; infer_instance
  have hbij := app_bijective R hR M G' G β hflat hpb.1
  have hloc : ∀ y : G.left, ∃ V : G.left.Opens, y ∈ V ∧ ∃ t : LB.Gen (P'.L.L.pull (β ⁻¹ᵁ V).ι), t.IsGen := by
    intro y
    by_cases hy : G.hom y = closedPoint R
    · obtain ⟨z, hzc, hyz, hz⟩ := exists_closed_spec R G hG.quasiCompact y hy
      obtain ⟨V, hzV, t⟩ := GlobalTheory.T.exists_generator_descendedBundle_near_closedPoint R hR M G' hG' P' G β hG hpb θ O hO hθ z hzc hz
      exact ⟨V, hyz.mem_open V.isOpen hzV, t⟩
    · exact GlobalTheory.T.exists_generator_off_closedFibre_descended R hR M G' hG' P' G β hG hpb θ O hO hθ y hy
  exact GlobalTheory.T.exists_lineBundle_descent_bijective_app _ _ β hbij P'.L.L P'.L.isLB hloc

end GlobalTheory.Mum.CubeDesc
