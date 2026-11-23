import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurveStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ProjFin

theorem isFractionRing_evaluation (X : Scheme.{0}) [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x = genericPoint X) (hxU : x ∈ U) :
    letI := (X.evaluation U x hxU).hom.toAlgebra
    IsFractionRing Γ(X, U) (X.residueField x) := by
  subst hx
  letI := (X.evaluation U _ hxU).hom.toAlgebra
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  let e : X.functionField ≃ₐ[Γ(X, U)] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective φ ⟨φ.injective, X.residue_surjective _⟩ with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e

theorem finrank_app_eq_residueDegree {Z Z' : Scheme.{0}} [IsIntegral Z] [IsIntegral Z']
    (f : Z' ⟶ Z) [IsFinite f] (h : f (genericPoint Z') = genericPoint Z) {U : Z.Opens}
    (hU : IsAffineOpen U) (hxU : f (genericPoint Z') ∈ U) :
    letI := (f.app U).hom.toAlgebra
    Module.finrank Γ(Z, U) Γ(Z', f ⁻¹ᵁ U) = f.residueDegree (genericPoint Z') := by
  letI := (f.app U).hom.toAlgebra
  letI := (Z.evaluation U _ hxU).hom.toAlgebra
  letI : Algebra Γ(Z', f ⁻¹ᵁ U) (Z'.residueField (genericPoint Z')) :=
    (Z'.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint Z')).hom.toAlgebra
  letI : Algebra Γ(Z, U) (Z'.residueField (genericPoint Z')) :=
    (f.app U ≫ Z'.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  haveI : IsScalarTower Γ(Z, U) Γ(Z', f ⁻¹ᵁ U) (Z'.residueField (genericPoint Z')) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(Z, U) (Z.residueField (f (genericPoint Z')))
      (Z'.residueField (genericPoint Z')) :=
    IsScalarTower.of_algebraMap_eq' congr($(Scheme.evaluation_naturality f _ hxU).hom).symm
  haveI := isFractionRing_evaluation Z hU h hxU
  haveI := isFractionRing_evaluation Z' (hU.preimage f) rfl hxU
  exact (IsFractionRing.finrank_eq Γ(Z, U) (Z.residueField (f (genericPoint Z')))
    Γ(Z', f ⁻¹ᵁ U) (Z'.residueField (genericPoint Z'))).symm

theorem genRank_eq_finrank_sections {X : Scheme.{0}} [IsIntegral X] (F : X.Modules)
    [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (hx : genericPoint X ∈ U) :
    VB.genRank F = Module.finrank Γ(X, U) Γ(F, U) := by
  haveI : Nonempty U := ⟨⟨_, hx⟩⟩
  have key (y : U) : Module.finrank (X.presheaf.stalk (y : X)) (F.presheaf.stalk (y : X) :) =
      Module.finrank Γ(X, U) Γ(F, U) := by
    have := hU.isLocalization_stalk y
    have := QCoh.isLocalizedModule_germLinear F hU y
    have hp := (hU.primeIdealOf y).asIdeal.primeCompl_le_nonZeroDivisors
    rw [IsLocalization.finrank_eq _ _ hp, IsLocalizedModule.finrank_eq _ (QCoh.germLinear F y) hp]
  exact key ⟨_, hx⟩

theorem isFiniteQC_pushforward_structureModule {Z Z' : Scheme.{0}} (f : Z' ⟶ Z) [IsFinite f] :
    QCoh.IsFiniteQC ((Scheme.Modules.pushforward f).obj (structureModule Z')) :=
  ⟨inferInstance, fun _ hV => QCoh.finite_sections_pushforward f _ hV
    (hF := QCoh.finite_sections (structureModule Z') (hV.preimage f))⟩

theorem genRank_pushforward {Z Z' : Scheme.{0}} [IsIntegral Z] [IsIntegral Z'] (f : Z' ⟶ Z)
    [IsFinite f] (h : f (genericPoint Z') = genericPoint Z) :
    VB.genRank ((Scheme.Modules.pushforward f).obj (structureModule Z')) =
      f.residueDegree (genericPoint Z') := by
  obtain ⟨U, hU, hxU⟩ := QCoh.exists_affine_mem (genericPoint Z)
  have hx' : f (genericPoint Z') ∈ U := h ▸ hxU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  have h1 : VB.genRank ((Scheme.Modules.pushforward f).obj (structureModule Z')) =
      Module.finrank Γ(Z, U) Γ((Scheme.Modules.pushforward f).obj (structureModule Z'), U) :=
    genRank_eq_finrank_sections _ hU hxU
  letI := (f.app U).hom.toAlgebra
  let e : Γ((Scheme.Modules.pushforward f).obj (structureModule Z'), U) ≃ₗ[Γ(Z, U)]
      Γ(Z', f ⁻¹ᵁ U) :=
    { toFun := fun s => s
      invFun := fun s => s
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [h1, e.finrank_eq, finrank_app_eq_residueDegree f h hU hx']

theorem interNumOn_eq_residueDegree_mul : ∀ (κ : Type) [Field κ] (Z Z' : Scheme.{0}) [IsIntegral Z]
    [IsIntegral Z'] [Algebra κ Γ(Z, ⊤)] (f : Z' ⟶ Z) [IsFinite f], IsProjOver (strHom κ Z) →
    topologicalKrullDim Z = 1 → f (genericPoint Z') = genericPoint Z → ∀ N : LB Z, N.IsLB →
    interNumOn κ f ![N] = (f.residueDegree (genericPoint Z') : ℤ) *
      interNum κ (structureModule Z) ![N] := by
  intro κ _ Z Z' _ _ _ f _ hP hd hg N hN
  haveI := isFiniteQC_pushforward_structureModule f
  rw [interNumOn_def, GlobalTheory.T.intersectionNumber_eq_genericRank_mul_projCurve κ Z hP hd _ N hN, genRank_pushforward f hg]

end GlobalTheory.ProjFin
