import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfQuasiIso
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConeRes

variable {C : Type*} [Category C] [Abelian C]

open DerivedCategory Pretriangulated in

theorem quasiIso_mappingCone_map {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) [QuasiIso a] [QuasiIso b] :
    QuasiIso (mappingCone.map φ₁ φ₂ a b comm) := by
  letI := HasDerivedCategory.standard C
  rw [← isIso_Q_map_iff_quasiIso]
  exact isIso₃_of_isIso₁₂ (Q.mapTriangle.map (mappingCone.triangleMap φ₁ φ₂ a b comm))
    (mappingCone_triangle_distinguished φ₁) (mappingCone_triangle_distinguished φ₂)
    (show IsIso (Q.map a) from inferInstance) (show IsIso (Q.map b) from inferInstance)

theorem homotopy_of_mk_eq {K L : CochainComplex C ℤ} {f g : K ⟶ L}
    (h : CohomologyClass.mk (Cocycle.ofHom f) = CohomologyClass.mk (Cocycle.ofHom g)) : Nonempty (Homotopy f g) := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (-1) (by omega)] at h
  obtain ⟨β, hβ⟩ := h
  refine ⟨(Cochain.equivHomotopy f g).symm ⟨β, ?_⟩⟩
  rw [hβ]
  simp

theorem quasiIso_of_homotopy {K L : CochainComplex C ℤ} {f g : K ⟶ L} (h : Homotopy f g) (hg : QuasiIso g) :
    QuasiIso f := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, h.homologyMap_eq]
  infer_instance

variable {R : Type} [CommRing R]

theorem mk_ofHom_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) :
    CohomologyClass.mk (Cocycle.ofHom (f ≫ g)) = cpull f M 0 (CohomologyClass.mk (Cocycle.ofHom g)) := by
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem resAug_comm {F G : Shv R} (φ : F ⟶ G) :
    (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G = resAug F ≫ resMap R φ :=
  (InjectiveResolution.Hom.ι'_comp_hom'
    (⟨InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F),
      InjectiveResolution.desc_commutes_zero φ _ _⟩ : InjectiveResolution.Hom _ _ φ)).symm

instance resAug_quasiIso (F : Shv R) : QuasiIso (resAug F) := (inferInstance : QuasiIso (injectiveResolution F).ι')

instance res_isKInjective (F : Shv R) : (res R F).IsKInjective :=
  inferInstanceAs ((injectiveResolution F).cochainComplex.IsKInjective)

theorem cone_isKInjective {F G : Shv R} (φ : F ⟶ G) : (mappingCone (resMap R φ)).IsKInjective := by
  haveI : ∀ n, Injective ((res R F).X n) := fun n => inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))
  haveI : ∀ n, Injective ((res R G).X n) := fun n => inferInstanceAs (Injective ((injectiveResolution G).cochainComplex.X n))
  haveI : (res R F).IsStrictlyGE 0 := inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)
  haveI : (res R G).IsStrictlyGE 0 := inferInstanceAs ((injectiveResolution G).cochainComplex.IsStrictlyGE 0)
  haveI : ∀ n, Injective ((mappingCone (resMap R φ)).X n) := fun n =>
    Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod (resMap R φ) n (n + 1) rfl).symm inferInstance
  haveI : (mappingCone (resMap R φ)).IsStrictlyGE (-1) := CochainComplex.isStrictlyGE_mappingCone _ 0 0 (-1)
  exact isKInjective_of_injective _ (-1)

end GlobalTheory.EtC.ConeRes

open GlobalTheory.EtC.ConeRes in

theorem GlobalTheory.EtC.cone_resMap_homotopyEquiv : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
    ∃ e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃),
      Nonempty (Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g)) := by
  intro R _ S hS
  have hS' : (S.map (CochainComplex.singleFunctor (Shv R) 0)).ShortExact :=
    hS.map_of_exact (HomologicalComplex.single _ _ _)
  haveI := mappingCone.quasiIso_descShortComplex hS'
  haveI := cone_isKInjective S.f
  let q := mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))
  let m := mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) (resAug_comm S.f)
  haveI : QuasiIso m := quasiIso_mappingCone_map _ _ _ _ _
  obtain ⟨c, hc⟩ := (GlobalTheory.EtC.cpull_bijective_of_quasiIso R m (res R S.X₃) 0).2
    (CohomologyClass.mk (Cocycle.ofHom (q ≫ resAug S.X₃)))
  obtain ⟨z, rfl⟩ := c.mk_surjective
  let u : mappingCone (resMap R S.f) ⟶ res R S.X₃ := Cocycle.homOf z
  have hz : z = Cocycle.ofHom u := (Cocycle.ofHom_homOf_eq_self z).symm
  rw [hz, ← mk_ofHom_comp] at hc
  obtain ⟨H1⟩ := homotopy_of_mk_eq hc
  haveI : QuasiIso (m ≫ u) := quasiIso_of_homotopy H1 ((quasiIso_iff_comp_left q (resAug S.X₃)).2 (resAug_quasiIso S.X₃))
  haveI : QuasiIso u := (quasiIso_iff_comp_left m u).1 inferInstance
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff u).1 inferInstance
  refine ⟨e, homotopy_of_mk_eq ?_⟩
  apply (GlobalTheory.EtC.cpull_bijective_of_quasiIso R (resAug S.X₂) (res R S.X₃) 0).1
  rw [← mk_ofHom_comp, ← mk_ofHom_comp, he]
  have hinr : mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫ m =
      resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) :=
    mappingCone.inr_desc ((CochainComplex.singleFunctor (Shv R) 0).map S.f) _ _ _
  have hq : mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫ q =
      (CochainComplex.singleFunctor (Shv R) 0).map S.g := mappingCone.inr_descShortComplex _
  have h1 : resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) ≫ u =
      mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫ m ≫ u :=
    ((reassoc_of% hinr) u).symm
  have h2 : mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫ q ≫ resAug S.X₃ =
      (CochainComplex.singleFunctor (Shv R) 0).map S.g ≫ resAug S.X₃ :=
    (reassoc_of% hq) (resAug S.X₃)
  exact ((congrArg (fun x => CohomologyClass.mk (Cocycle.ofHom x)) h1).trans (mk_ofHom_comp _ _)).trans
    ((congrArg (cpull _ _ 0) hc).trans ((mk_ofHom_comp _ _).symm.trans
      ((congrArg (fun x => CohomologyClass.mk (Cocycle.ofHom x)) h2).trans
        (congrArg (fun x => CohomologyClass.mk (Cocycle.ofHom x)) (resAug_comm S.g)))))
