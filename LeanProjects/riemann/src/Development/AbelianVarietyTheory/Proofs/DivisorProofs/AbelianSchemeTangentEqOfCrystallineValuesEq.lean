import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamComparisonBijectiveCupSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorFunctionalGlobalFormsAbelianS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormValueOnTangentVectorEqZeroOfGlobalFormZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraFiniteProjectiveRank
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsDetEquivOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieInj

open GlobalTheory.CechDR

variable {R : Type} [CommRing R]

theorem cmpForm_surjective (hP : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hdim : SmoothOfRelativeDimension g A.hom) :
    Function.Surjective (cmpForm (A.hom ≫ 𝟙 (Sp R))) := by
  intro ω
  obtain ⟨-, hinj, -⟩ := (hH R A g hab hdim).2.2.2.2.1
  haveI := hab.smooth
  haveI := hab.proper
  have hb := (cechDeRham_comparison_bijective_cup_smooth hP R A.left (A.hom ≫ 𝟙 (Sp R)) inferInstance inferInstance
    inferInstance).1
  obtain ⟨c, hc⟩ := hb.2 (clForm _ ω)
  have hmem : clForm (A.hom ≫ 𝟙 (Sp R)) ω ∈ CechHodgeFiltration (A.hom ≫ 𝟙 (Sp R)) := by
    rw [cechHodgeFiltration_eq_range]; exact ⟨ω, rfl⟩
  have h0 : toHO1 _ (cmp1 (A.hom ≫ 𝟙 (Sp R)) c) = 0 := by rw [hc]; exact hmem
  rw [structureSheaf_comparison_comm] at h0
  have h1 : toH1O _ c = 0 := GlobalTheory.CechDR.cmpO_injective R A.left _ (h0.trans (map_zero _).symm)
  have h2 : c ∈ F1 (A.hom ≫ 𝟙 (Sp R)) := h1
  rw [hodgeFiltration_eq_range] at h2
  obtain ⟨f, rfl⟩ := h2
  refine ⟨f, hinj ?_⟩
  change clForm (A.hom ≫ 𝟙 (Sp R)) (cmpForm _ f) = clForm (A.hom ≫ 𝟙 (Sp R)) ω
  rw [← comparison_formClass, hc]

section Lie

open ReciprocityTheory.ChartRestriction.G MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

theorem lie_finite_projective (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (g : ℕ)
    (hdim : SmoothOfRelativeDimension g A.hom) (a : OAct ℤ A) :
    Module.Finite R (GlobalTheory.Serre.Lie a) ∧ Module.Projective R (GlobalTheory.Serre.Lie a) ∧
      ∀ p, Module.rankAtStalk (R := R) (GlobalTheory.Serre.Lie a) p = g := by
  haveI : Smooth A.hom := hdim.smooth
  refine GlobalTheory.LieProj.finite_projective_of_localBasis (M := GlobalTheory.Serre.Lie a) g fun p ↦ ?_
  obtain ⟨r, hr, ⟨C⟩, v, hv⟩ := GlobalTheory.LieProj.exists_chart_lieBasis A g hdim p
  refine ⟨r, hr, ?_⟩
  obtain ⟨a', -⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback a
    (isGrpPullback_pullback A (ReciprocityTheory.ChartRestriction.G.Chart.fB R (Localization.Away r)))
  obtain ⟨e⟩ := GlobalTheory.LieAway.lie_away A a r a' ⟨C⟩
  exact ⟨(GlobalTheory.Serre.Lie.basis a' hv).map e.symm⟩

end Lie

def valMap (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (a : OAct ℤ A) :
    GlobalTheory.Serre.Lie a →ₗ[R] Module.Dual R (Form (A.hom ≫ 𝟙 (Sp R))) where
  toFun v := tanVal v.hom
  map_add' v w := LinearMap.ext fun f ↦ by
    rw [LinearMap.add_apply, ← tanVal_mul v.isTangent w.isTangent, GlobalTheory.Serre.Lie.hom_add]
  map_smul' r v := LinearMap.ext fun f ↦ by
    rw [LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, ← tanVal_epsScale, GlobalTheory.Serre.Lie.hom_smul]

theorem valMap_mem (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (a : OAct ℤ A) (u : GlobalTheory.Serre.Lie a) :
    valMap A a u ∈ (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro f hf
  exact GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero R A u.hom f hf

theorem valMap_surjective (hP : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hdim : SmoothOfRelativeDimension g A.hom) [IsCommMonObj A] (a : OAct ℤ A) :
    Function.Surjective ((valMap A a).codRestrict _ (valMap_mem A a)) := by
  have hex := GlobalTheory.LieDual.exists_tangent_of_functional hP hH R A g hab hdim
  have key : ∀ φ : Module.Dual R (Form (A.hom ≫ 𝟙 (Sp R))),
      (∀ f, cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → φ f = 0) → ∃ u : GlobalTheory.Serre.Lie a, valMap A a u = φ := by
    intro φ hφ
    obtain ⟨u, hu, hu'⟩ := hex φ hφ
    exact ⟨GlobalTheory.Serre.Lie.mk a u hu, LinearMap.ext hu'⟩
  intro ψ
  have hψ : ∀ f, cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → ψ.1 f = 0 := fun f hf ↦
    (Submodule.mem_dualAnnihilator ψ.1).1 ψ.2 f (LinearMap.mem_ker.2 hf)
  exact (key ψ.1 hψ).imp fun u hu ↦ Subtype.ext hu

theorem tangent_eq_of_tanVal_eq : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham →
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom → ∀ v w : epsR R ⟶ A, IsTangent v → IsTangent w →
        (∀ f : Form (A.hom ≫ 𝟙 (Sp R)), tanVal v f = tanVal w f) → v = w := by
  intro hP hH R _ A _ g hab hdim v w hv hw hvw
  haveI : IsCommMonObj A := hab.comm
  have hT := lie_finite_projective A g hdim (GlobalTheory.Serre.intAct A)
  haveI := hT.1
  haveI := hT.2.1
  have hcl : ClosedForm (A.hom ≫ 𝟙 (Sp R)) = ⊤ := (hH R A g hab hdim).2.2.2.2.1.1
  have hG := (hH R A g hab hdim).2.2.1
  haveI : Module.Finite R (GlobForm (A.hom ≫ 𝟙 (Sp R))) := hG.1
  haveI : Module.Projective R (GlobForm (A.hom ≫ 𝟙 (Sp R))) := hG.2.1
  have e1 : (Form (A.hom ≫ 𝟙 (Sp R)) ⧸ LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))) ≃ₗ[R]
      GlobForm (A.hom ≫ 𝟙 (Sp R)) :=
    ((cmpForm (A.hom ≫ 𝟙 (Sp R))).quotKerEquivOfSurjective
      (cmpForm_surjective hP hH A g hab hdim)).trans (LinearEquiv.ofTop _ hcl)
  have eN : (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator ≃ₗ[R]
      Module.Dual R (GlobForm (A.hom ≫ 𝟙 (Sp R))) :=
    (Submodule.dualQuotEquivDualAnnihilator _).symm.trans e1.symm.dualMap
  haveI : Module.Finite R (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator :=
    Module.Finite.equiv eN.symm
  haveI : Module.Projective R (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator :=
    Module.Projective.of_equiv eN.symm
  have hbij := Module.bijective_of_surjective_of_rankAtStalk_eq
    (valMap_surjective hP hH A g hab hdim (GlobalTheory.Serre.intAct A)) fun m _ ↦ by
      rw [hT.2.2, congrFun (Module.rankAtStalk_eq_of_equiv eN) _, GlobalTheory.TopExt.rankAtStalk_dual]
      exact (hG.2.2 _).symm
  have h := hbij.1 (a₁ := GlobalTheory.Serre.Lie.mk (GlobalTheory.Serre.intAct A) v hv)
    (a₂ := GlobalTheory.Serre.Lie.mk (GlobalTheory.Serre.intAct A) w hw) (Subtype.ext (LinearMap.ext hvw))
  exact congrArg GlobalTheory.Serre.Lie.hom h

end GlobalTheory.LieInj
