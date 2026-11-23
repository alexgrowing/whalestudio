import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyResolutionsResidueFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeBaseChangeEqFinrankRangeDualMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KoszulResolutionThreeTermsExactStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsRegularOfFnOfRingKrullDimQuotientAddLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ProjectiveOfIsLocallyConstantFinrankFiber
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FirstBetti

theorem finrank_homology_succ_add (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K]
    (C : CochainComplex (ModuleCat.{0} O) ℕ) [∀ i, Module.Finite O (C.X i)] (n : ℕ) :
    Module.finrank K ((((ModuleCat.extendScalars (algebraMap O K)).mapHomologicalComplex _).obj
        C).homology (n + 1))
      + Module.finrank K (LinearMap.range ((C.d n (n + 1)).hom.baseChange K))
      + Module.finrank K (LinearMap.range ((C.d (n + 1) (n + 2)).hom.baseChange K))
      = Module.finrank K (K ⊗[O] C.X (n + 1)) := by
  let D := ((ModuleCat.extendScalars (algebraMap O K)).mapHomologicalComplex _).obj C
  have e1 := (D.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).toLinearEquiv
  obtain ⟨e2⟩ := GlobalTheory.Semicont.nonempty_homology_map_extendScalars_equiv K (C.sc' n (n + 1) (n + 2))
  have h := GlobalTheory.Semicont.finrank_homology_add_finrank_range
    ((C.d n (n + 1)).hom.baseChange K) ((C.d (n + 1) (n + 2)).hom.baseChange K)
    (by rw [← LinearMap.baseChange_comp, ← ModuleCat.hom_comp, C.d_comp_d, ModuleCat.hom_zero,
      LinearMap.baseChange_zero])
  rw [(e1.trans e2).finrank_eq]
  exact h

theorem smul_eq_zero_of_algebraMap_eq_zero {O : Type} [CommRing O] {K : Type} [Field K]
    [Algebra O K] {M : Type} [AddCommGroup M] [Module O M] {r : O} (hr : algebraMap O K r = 0)
    (z : K ⊗[O] M) : r • z = 0 := by
  rw [← algebraMap_smul K r z, hr, zero_smul]

theorem baseChange_eq_zero_of_ring {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
    {M : Type} [AddCommGroup M] [Module O M] (e : M →ₗ[O] O)
    (he : ∀ x, algebraMap O K (e x) = 0) : e.baseChange K = 0 := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k x =>
    rw [LinearMap.baseChange_tmul, LinearMap.zero_apply, ← mul_one (e x), ← smul_eq_mul,
      TensorProduct.tmul_smul, smul_eq_zero_of_algebraMap_eq_zero (he x)]
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.zero_apply, add_zero]

theorem baseChange_eq_zero_of_pi {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
    {M : Type} [AddCommGroup M] [Module O M] {n : ℕ} (e : M →ₗ[O] (Fin n → O))
    (he : ∀ x i, algebraMap O K (e x i) = 0) : e.baseChange K = 0 := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k x =>
    rw [LinearMap.baseChange_tmul, LinearMap.zero_apply, pi_eq_sum_univ (e x),
      TensorProduct.tmul_sum]
    exact Finset.sum_eq_zero fun i _ => by
      rw [TensorProduct.tmul_smul, smul_eq_zero_of_algebraMap_eq_zero (he x i)]
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.zero_apply, add_zero]

end GlobalTheory.FirstBetti

namespace GlobalTheory

open FirstBetti in

theorem finrank_homology_one_two_of_dual_resolution : ∀ (O : Type) [CommRing O] [IsRegularLocalRing O] (g : ℕ), ringKrullDim O = g → ∀ (f : Fin g → O), Ideal.span (Set.range f) ≠ ⊤ → IsArtinianRing (O ⧸ Ideal.span (Set.range f)) → ∀ (C : CochainComplex (ModuleCat.{0} O) ℕ), (∀ i, Module.Free O (C.X i) ∧ Module.Finite O (C.X i)) → (∀ i, Function.Exact (C.d (i + 1) (i + 2)).hom.dualMap (C.d i (i + 1)).hom.dualMap) → Nonempty ((Module.Dual O (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[O] (O ⧸ Ideal.span (Set.range f))) → ∀ (K : Type) [Field K] (φ : O →+* K), RingHom.ker φ = IsLocalRing.maximalIdeal O → Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 1) = g ∧ Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 2) ≤ g.choose 2 := by
  intro O _ _ g hdim f hne hart C hC hex hN K _ φ hker
  obtain ⟨eN⟩ := hN
  letI := φ.toAlgebra
  haveI : ∀ i, Module.Free O (C.X i) := fun i => (hC i).1
  haveI : ∀ i, Module.Finite O (C.X i) := fun i => (hC i).2
  have hIm : Ideal.span (Set.range f) ≤ IsLocalRing.maximalIdeal O := IsLocalRing.le_maximalIdeal hne
  have hIφ : ∀ x ∈ Ideal.span (Set.range f), algebraMap O K x = 0 := fun x hx => by
    have : x ∈ RingHom.ker φ := hker ▸ hIm hx
    exact this

  have hreg : RingTheory.Sequence.IsRegular O (List.ofFn f) := by
    refine GlobalTheory.isRegular_ofFn_of_ringKrullDim_quotient_add_le O g g f hdim
      (fun i => hIm (Ideal.subset_span ⟨i, rfl⟩)) ?_
    have h0 : ringKrullDim (O ⧸ Ideal.span (Set.range f)) ≤ 0 := Ring.krullDimLE_iff.1 inferInstance
    calc ringKrullDim (O ⧸ Ideal.span (Set.range f)) + (g : WithBot ℕ∞) ≤ 0 + (g : WithBot ℕ∞) :=
          add_le_add_left h0 _
      _ = g := zero_add _
  obtain ⟨e₁, e₂, hx1, hx2, he1, he2⟩ := GlobalTheory.T.koszul_resolution_three_terms_exact O g f hreg.toIsWeaklyRegular

  let ε : Module.Dual O (C.X 0) →ₗ[O] O ⧸ Ideal.span (Set.range f) :=
    eN.toLinearMap ∘ₗ (LinearMap.range (C.d 0 1).hom.dualMap).mkQ
  have hεs : Function.Surjective ε := eN.surjective.comp (Submodule.mkQ_surjective _)
  have hεx : Function.Exact (C.d 0 1).hom.dualMap ε := by
    rw [LinearMap.exact_iff, LinearEquiv.ker_comp, Submodule.ker_mkQ]
  obtain ⟨hA, hB⟩ := GlobalTheory.T.finrank_homology_resolutions_residueField O K (O ⧸ Ideal.span (Set.range f))
    (Module.Dual O (C.X 0)) (Module.Dual O (C.X 1)) (Module.Dual O (C.X 2)) (Module.Dual O (C.X 3))
    O (Fin g → O) (Fin (g.choose 2) → O) ε (C.d 0 1).hom.dualMap (C.d 1 2).hom.dualMap
    (C.d 2 3).hom.dualMap (Ideal.span (Set.range f)).mkQ e₁ e₂ hεs hεx (hex 0) (hex 1)
    (Submodule.mkQ_surjective _) hx1 hx2

  have hz1 : e₁.baseChange K = 0 := baseChange_eq_zero_of_ring e₁ fun x => hIφ _ (he1 x)
  have hz2 : e₂.baseChange K = 0 := baseChange_eq_zero_of_pi e₂ fun x i => hIφ _ (he2 x i)
  have hk1 : Module.finrank K (LinearMap.ker (e₁.baseChange K)) = g := by
    rw [hz1, LinearMap.ker_zero, finrank_top, GlobalTheory.Semicont.finrank_baseChange_fin]
  have hr2 : Module.finrank K (LinearMap.range (e₂.baseChange K)) = 0 := by
    rw [hz2, LinearMap.range_zero, finrank_bot]
  have hc2 : Module.finrank K (K ⊗[O] (Fin (g.choose 2) → O)) = g.choose 2 :=
    GlobalTheory.Semicont.finrank_baseChange_fin _ _

  obtain ⟨r0, n0⟩ := GlobalTheory.T.finrank_range_baseChange_eq_finrank_range_dualMap O K (C.X 0) (C.X 1) (C.d 0 1).hom
  obtain ⟨r1, n1⟩ := GlobalTheory.T.finrank_range_baseChange_eq_finrank_range_dualMap O K (C.X 1) (C.X 2) (C.d 1 2).hom
  obtain ⟨r2, n2⟩ := GlobalTheory.T.finrank_range_baseChange_eq_finrank_range_dualMap O K (C.X 2) (C.X 3) (C.d 2 3).hom
  have k1 := LinearMap.finrank_range_add_finrank_ker ((C.d 0 1).hom.dualMap.baseChange K)
  have k2 := LinearMap.finrank_range_add_finrank_ker ((C.d 1 2).hom.dualMap.baseChange K)

  have h1 : Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 1)
      + Module.finrank K (LinearMap.range ((C.d 0 1).hom.baseChange K))
      + Module.finrank K (LinearMap.range ((C.d 1 2).hom.baseChange K))
      = Module.finrank K (K ⊗[O] C.X 1) := finrank_homology_succ_add O K C 0
  have h2 : Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 2)
      + Module.finrank K (LinearMap.range ((C.d 1 2).hom.baseChange K))
      + Module.finrank K (LinearMap.range ((C.d 2 3).hom.baseChange K))
      = Module.finrank K (K ⊗[O] C.X 2) := finrank_homology_succ_add O K C 1
  constructor <;> omega

end GlobalTheory
