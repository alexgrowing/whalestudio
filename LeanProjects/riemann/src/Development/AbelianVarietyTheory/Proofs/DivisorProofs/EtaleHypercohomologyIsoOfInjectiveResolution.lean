import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.InjResCmp

variable {R : Type} [CommRing R]

theorem cpush_id (K I : Cx R) (n : ℤ) (x : CohomologyClass K I n) : cpush K (𝟙 I) n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem cpush_comp (K : Cx R) {I J L : Cx R} (f : I ⟶ J) (g : J ⟶ L) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (f ≫ g) n x = cpush K g n (cpush K f n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem cpush_homotopy (K : Cx R) {I J : Cx R} {f g : I ⟶ J} (h : Homotopy f g) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K f n x = cpush K g n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g h
  change CohomologyClass.mk _ = CohomologyClass.mk _
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨x.1.comp z (by omega), ?_⟩
  rw [δ_comp x.1 z (by omega) (n + 1) 0 n (by omega) (by omega) (by omega)]
  simp [zcomp, hz, Cochain.comp_add]

open DerivedCategory in
theorem exists_quasiIso (M : Shv R) (C : Cx R) (ε : sgl M ⟶ C) [QuasiIso ε] [(res R M).IsKInjective] :
    ∃ u : C ⟶ res R M, QuasiIso u := by
  letI := HasDerivedCategory.standard (Shv R)
  have : QuasiIso (resAug M) := (inferInstance : QuasiIso (injectiveResolution M).ι')
  let e : Q.obj C ≅ Q.obj (res R M) := (asIso (Q.map ε)).symm ≪≫ asIso (Q.map (resAug M))
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj C)
    (res R M)).surjective
    ((quotientCompQhIso (Shv R)).hom.app C ≫ e.hom ≫ (quotientCompQhIso (Shv R)).inv.app (res R M))
  obtain ⟨u, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨u, ?_⟩
  rw [← isIso_Q_map_iff_quasiIso]
  have h1 := quotientCompQhIso_hom_naturality u
  have h2 : Q.map u = (quotientCompQhIso (Shv R)).inv.app C ≫ Qh.map ((HomotopyCategory.quotient _ _).map u) ≫
      (quotientCompQhIso (Shv R)).hom.app (res R M) := by
    rw [h1]; simp
  rw [h2, hg]
  infer_instance

theorem hyper_iso_of_injective_resolution : ∀ (R : Type) [CommRing R] (M : Shv R) (C : Cx R) (ε : sgl M ⟶ C),
    C.IsStrictlyGE 0 → (∀ t, Injective (C.X t)) → QuasiIso ε → ∀ (K : Cx R) (n : ℤ),
    Nonempty (HK R K M n ≃+ CohomologyClass K C n) := by
  intro R _ M C ε hC hI hε K n
  haveI := hC
  haveI : ∀ t, Injective (C.X t) := hI
  haveI := hε
  haveI : C.IsKInjective := isKInjective_of_injective C 0
  haveI : (res R M).IsKInjective := (inferInstance : (injectiveResolution M).cochainComplex.IsKInjective)
  obtain ⟨u, hu⟩ := exists_quasiIso M C ε
  obtain ⟨e, -⟩ := (CochainComplex.IsKInjective.quasiIso_iff u).1 hu
  exact ⟨{ toFun := cpush K e.inv n
           invFun := cpush K e.hom n
           left_inv := fun x => by
             change cpush K e.hom n (cpush K e.inv n x) = x
             rw [← cpush_comp, cpush_homotopy K e.homotopyInvHomId, cpush_id]
           right_inv := fun y => by
             change cpush K e.inv n (cpush K e.hom n y) = y
             rw [← cpush_comp, cpush_homotopy K e.homotopyHomInvId, cpush_id]
           map_add' := map_add _ }⟩

end GlobalTheory.EtC.InjResCmp
