import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCoverStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.PicMain
import Development.AutomorphicArithmetic.CommutativeAlgebra.PicUnit
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsUniqueSectionOfEtaleFaithfullyFlatDescent
import Development.AutomorphicArithmetic.CommutativeAlgebra.UnitSectionsMultiplicativeGroupBijectiveAffine
import Development.AutomorphicArithmetic.CommutativeAlgebra.MultiplicativeGroupOneCocycleEtaleLocallyCobound

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace UpperTheory.PicD

private def SF (F : Shv ℤ) : CommRingCat.{0} ⥤ AddCommGrpCat.{1} :=
  Scheme.Spec.rightOp ⋙ F.obj ⋙ forget₂ (ModuleCat.{1} (ULift.{1} ℤ)) AddCommGrpCat.{1}

private def SFd {F G : Shv ℤ} (φ : F ⟶ G) : SF F ⟶ SF G :=
  Functor.whiskerLeft _ (Functor.whiskerRight φ.hom _)

private theorem res_res (F : Shv ℤ) {R S T : CommRingCat.{0}} (f : R ⟶ S) (g : S ⟶ T) (x : Sec F (Spec R)) :
    (Sec.res (Spec.map g) (Sec.res (Spec.map f) x) : Sec F (Spec T)) = Sec.res (Spec.map (f ≫ g)) x := by
  show (F.obj.map (Spec.map g).op).hom ((F.obj.map (Spec.map f).op).hom x) =
    (F.obj.map (Spec.map (f ≫ g)).op).hom x
  rw [Spec.map_comp, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

private def uS (R : CommRingCat.{0}) (u : Rˣ) : Sec Gm (Spec R) :=
  unitSec (Units.map (Scheme.ΓSpecIso R).inv.hom.toMonoidHom u)

private theorem uS_mul (R : CommRingCat.{0}) (u v : Rˣ) : uS R (u * v) = uS R u + uS R v := by
  unfold uS
  rw [map_mul, unitSec_mul]

private theorem uS_res {R S : CommRingCat.{0}} (f : R ⟶ S) (u : Rˣ) :
    Sec.res (Spec.map f) (uS R u) = uS S (Units.map f.hom.toMonoidHom u) := by
  unfold uS
  rw [unitSec_res]
  congr 1
  ext
  change ((Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop).hom (u : R) =
    (f ≫ (Scheme.ΓSpecIso S).inv).hom (u : R)
  rw [Scheme.ΓSpecIso_inv_naturality]

private theorem uS_bij (R : CommRingCat.{0}) : Function.Bijective (uS R) := by
  have h2 : Function.Bijective (Units.map (Scheme.ΓSpecIso R).inv.hom.toMonoidHom) := by
    let e : R ≃+* Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
    exact (Units.mapEquiv e.toMulEquiv).bijective
  have h1 : Function.Bijective (unitSec (U := Spec R)) := UpperTheory.unitSections_multiplicativeGroup_bijective_affine R
  exact h1.comp h2

private def PD : Data where
  S0 := SF ((res ℤ Gm).X 0)
  S1 := SF ((res ℤ Gm).X 1)
  d := SFd ((res ℤ Gm).d 0 1)
  ι R := AddMonoidHom.mk' (fun u => (Sec.map (resι ℤ Gm) (uS R u.toMul) : Sec ((res ℤ Gm).X 0) (Spec R)))
    (fun u v => by
      show (Sec.map (resι ℤ Gm) (uS R (u.toMul * v.toMul)) : Sec ((res ℤ Gm).X 0) (Spec R)) = _
      rw [uS_mul]
      exact map_add _ _ _)
  ι_nat {R R'} f u := by
    have h := congrArg (fun φ => φ.hom (uS R u)) ((resι ℤ Gm).hom.naturality (Spec.map f).op)
    refine Eq.trans h.symm ?_
    show (Sec.map (resι ℤ Gm) (Sec.res (Spec.map f) (uS R u)) : Sec ((res ℤ Gm).X 0) (Spec R')) = _
    rw [uS_res]
    rfl
  ι_inj R u v h := by
    have h1 := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ Gm (Spec R)).2.1 h
    exact Additive.toMul.injective ((uS_bij R).1 h1)
  d_eq_zero R w := by
    have h := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ Gm (Spec R)).1 w
    constructor
    · intro h0
      obtain ⟨a, ha⟩ := h.1 h0
      obtain ⟨u, rfl⟩ := (uS_bij R).2 a
      exact ⟨Additive.ofMul u, ha⟩
    · rintro ⟨u, hu⟩
      exact h.2 ⟨_, hu⟩
  glue A C _ _ _ _ _ w hw := (UpperTheory.existsUnique_section_of_etale_faithfullyFlat_descent ℤ ((res ℤ Gm).X 0) A C w hw).exists
  sep A C _ _ _ _ _ y y' hy := by
    refine (UpperTheory.existsUnique_section_of_etale_faithfullyFlat_descent ℤ ((res ℤ Gm).X 1) A C _ ?_).unique (y₁ := y) (y₂ := y') rfl hy.symm
    have hc : CommRingCat.ofHom (algebraMap A C) ≫ CommRingCat.ofHom (i1 A C).toRingHom =
        CommRingCat.ofHom (algebraMap A C) ≫ CommRingCat.ofHom (i2 A C).toRingHom := by
      ext a
      exact ((i1 A C).commutes a).trans ((i2 A C).commutes a).symm
    have hk : ∀ (y0 : Sec ((res ℤ Gm).X 1) (Spec (CommRingCat.of A))),
        (Sec.res (Spec.map (CommRingCat.ofHom (i1 A C).toRingHom))
          (Sec.res (Spec.map (CommRingCat.ofHom (algebraMap A C))) y0) :
            Sec ((res ℤ Gm).X 1) (Spec (CommRingCat.of (TensorProduct A C C)))) =
        Sec.res (Spec.map (CommRingCat.ofHom (i2 A C).toRingHom))
          (Sec.res (Spec.map (CommRingCat.ofHom (algebraMap A C))) y0) := fun y0 => by
      rw [res_res, res_res, hc]
    exact hk y

end UpperTheory.PicD

set_option maxHeartbeats 1000000 in
open UpperTheory.PicD in
theorem UpperTheory.exists_injective_h1_gm_to_pic :
    ∀ (A : Type) [CommRing A], ∃ φ : H ℤ (sp A) Gm 1 →+ Additive (CommRing.Pic A), Function.Injective φ := by
  intro A _
  let X := Spec (CommRingCat.of A)
  let Z : AddSubgroup (PD.S1.obj (CommRingCat.of A)) :=
    ((SFd ((res ℤ Gm).d 1 2)).app (CommRingCat.of A)).hom.ker
  have hZ : ∀ z ∈ Z, PD.LocEx z := fun z hz => UpperTheory.multiplicativeGroup_oneCocycle_etaleLocally_coboundary A z hz
  obtain ⟨ψ, hψ⟩ := PD.main A Z hZ
  have hT := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff ℤ X (res ℤ Gm) 0 1 2 (by norm_num) (by norm_num)
  let e : Cocycle ((chains ℤ).obj (sp A)) (res ℤ Gm) 1 → Sec ((res ℤ Gm).X 1) X :=
    fun α => ev (α : Cochain ((chains ℤ).obj (sp A)) (res ℤ Gm) 1) 0 1 (by norm_num) X (𝟙 X)
  have hmem : ∀ α, e α ∈ Z := fun α => AddMonoidHom.mem_ker.mpr (hT.2 α).1
  let τ : Cocycle ((chains ℤ).obj (sp A)) (res ℤ Gm) 1 →+ Z :=
    { toFun := fun α => ⟨e α, hmem α⟩
      map_zero' := by
        ext
        exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties ℤ).1 (0 : Cochain ((chains ℤ).obj (sp A)) (res ℤ Gm) 1)
          0 0 1 (by norm_num) X (𝟙 X)).2.2.1
      map_add' := by
        intro α β
        ext
        exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties ℤ).1 (α : Cochain ((chains ℤ).obj (sp A)) (res ℤ Gm) 1)
          β 0 1 (by norm_num) X (𝟙 X)).1 }
  have hf : coboundaries ((chains ℤ).obj (sp A)) (res ℤ Gm) 1 ≤ (ψ.comp τ).ker := by
    intro α hα
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, hψ]
    exact ((hT.2 α).2.mp ((CohomologyClass.mk_eq_zero_iff α).mpr hα))
  refine ⟨CohomologyClass.descAddMonoidHom (ψ.comp τ) hf, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective c
  rw [CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.comp_apply, hψ] at hc
  exact (hT.2 α).2.mpr hc
