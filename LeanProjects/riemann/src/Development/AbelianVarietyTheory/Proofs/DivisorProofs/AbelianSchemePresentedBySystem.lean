import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCohomologyIsoPresentedCrystalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePairRestrictionInjectiveFirstCohomology

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_isCompl_ker_of_projective {R : Type} {M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Projective R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    ∃ C : Submodule R M, IsCompl (LinearMap.ker f) C := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfg : ∀ y, f (g y) = y := fun y ↦ LinearMap.congr_fun hg y
  refine ⟨LinearMap.range g, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨y, rfl⟩
    have : y = 0 := (hfg y).symm.trans hx
    rw [this, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have e : x = (x - g (f x)) + g (f x) := by abel
    rw [e]
    refine Submodule.add_mem_sup ?_ (LinearMap.mem_range_self g _)
    rw [LinearMap.mem_ker, map_sub, hfg, sub_self]

theorem mem_smul_top_of_tmul_eq_zero {R R₀ M : Type} [CommRing R] [CommRing R₀] [AddCommGroup M] [Module R M]
    (π : R →+* R₀) (hπ : Function.Surjective π) {I : Ideal R} (hk : RingHom.ker π = I) (x : M)
    (h : letI := π.toAlgebra; (1 : R₀) ⊗ₜ[R] x = 0) : x ∈ I • (⊤ : Submodule R M) := by
  letI := π.toAlgebra
  subst hk
  let f : (R ⧸ RingHom.ker π) ≃ₐ[R] R₀ :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R R₀) hπ
  let E : R₀ ⊗[R] M ≃ₗ[R] M ⧸ (RingHom.ker π) • (⊤ : Submodule R M) :=
    (TensorProduct.congr f.toLinearEquiv.symm (LinearEquiv.refl R M)).trans
      (TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker π))
  have h1 : E ((1 : R₀) ⊗ₜ[R] x) = Submodule.Quotient.mk x := by
    have : f.symm (1 : R₀) = Ideal.Quotient.mk _ 1 := by rw [map_one, map_one]
    change TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker π) (f.symm 1 ⊗ₜ[R] x) = _
    rw [this, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  rw [h, map_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at h1
  exact h1

theorem full_and_isCompl : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ S : Sys I π A₀.hom, S.Presents A'.hom i' → S.Full hI ∧ ∃ N, IsCompl (S.K hI) N := by
  intro H HD R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg S hS
  have hpb : IsPullback i' A₀.hom A'.hom (spMap π) := h'.1
  obtain ⟨e, he1, he2⟩ := GlobalTheory.T.hodge_cohomology_iso_presented_crystal R R₀ I hI π hπ hk A₀.left A₀.hom S A'.left A'.hom i' hpb hS
  have hsm : Smooth A'.hom := hA.smooth
  haveI : IsProper A'.hom := hA.proper
  have hsep : IsSeparated A'.hom := inferInstance
  have hqc : QuasiCompact A'.hom := inferInstance
  have hw : i' ≫ A'.hom = (A₀.hom ≫ spMap π) ≫ spMap (RingHom.id R) := by
    rw [Cris.spMap_id, Category.comp_id]; exact hpb.w
  let m : IsMor (dp0 R) A'.hom (divided₂ hI) (A₀.hom ≫ spMap π) (RingHom.id R) i' := IsMor.of_dividedPowersZeroIdeal _ hw
  have hm := (H.toCrystallineDeRham R I (divided₂ hI) (isDPNilpotent_squareZero hI) R₀ π hπ hk A'.left A₀.left A'.hom A₀.hom i'
    hsm hsep hqc hpb m).1
  have hc := H.bijective_cechDeRhamComparison_degreeOne A'.hom hsm hsep hqc
  obtain ⟨-, -, -, ⟨-, hproj, -⟩, ⟨-, -, hto⟩, hbc⟩ := HD R A' g hA hg
  have key : ∀ c, S.r hI (m.pull1 c) = e (toHO1 A'.hom (cmp1 A'.hom c)) := fun c ↦ (he1 m c).symm
  have hr : Function.Surjective (S.r hI) := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨w, rfl⟩ := hto x
    obtain ⟨c, rfl⟩ := hc.2 w
    exact ⟨m.pull1 c, key c⟩
  haveI : Module.Projective R (GlobalTheory.CatCoh.H1 S.F) := Module.Projective.of_equiv e
  refine ⟨?_, exists_isCompl_ker_of_projective (S.r hI) hr⟩
  intro z hz
  have hz0 : S.redO.pullbackOneCocycle z = 0 := by
    refine Subtype.ext (funext fun U ↦ funext fun V ↦ funext fun a ↦ ?_)
    exact (S.ker V _).2 (hz U V a)
  have h0 : S.redO.pull1 (H1.mk _ z) = 0 := by
    rw [CoefMap.pullCohomologyOne_class, hz0, map_zero]
  set x := e.symm (H1.mk _ z) with hxdef
  have hx0 : IsPullO hpb.w x 0 := by
    have := he2 x
    rwa [hxdef, LinearEquiv.apply_symm_apply, h0] at this
  letI := π.toAlgebra
  obtain ⟨-, -, e', he'⟩ := hbc R₀ A₀.left A₀.hom i' hpb
  have h1 : e' ((1 : R₀) ⊗ₜ[R] x) = 0 := by
    have a := he' x
    unfold IsPullO at a hx0
    exact (pairRes_injective i' A₀.hom).1 (a.symm.trans (hx0.trans (map_zero _).symm))
  have hxI : x ∈ I • (⊤ : Submodule R (HO1 A'.hom)) :=
    mem_smul_top_of_tmul_eq_zero π hπ hk x ((LinearEquiv.map_eq_zero_iff e').1 h1)
  have hzI : H1.mk _ z ∈ I • (⊤ : Submodule R (GlobalTheory.CatCoh.H1 S.F)) := by
    have : H1.mk _ z = e x := by rw [hxdef, LinearEquiv.apply_symm_apply]
    rw [this]
    have hm' : e.toLinearMap x ∈ Submodule.map e.toLinearMap (I • ⊤) := Submodule.mem_map_of_mem hxI
    rw [Submodule.map_smul''] at hm'
    exact Submodule.smul_mono le_rfl le_top hm'
  have hsurjI : Submodule.map (S.r hI) (I • ⊤) = I • (⊤ : Submodule R (GlobalTheory.CatCoh.H1 S.F)) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hr]
  rw [← hsurjI] at hzI
  obtain ⟨c, hc, hcz⟩ := hzI
  exact ⟨c, hc, hcz⟩

end GlobalTheory.LiftSys
