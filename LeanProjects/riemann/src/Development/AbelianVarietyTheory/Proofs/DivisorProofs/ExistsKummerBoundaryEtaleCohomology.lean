import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSequenceEtaleTateTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyBijectiveOfSupportBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyCoefficientMapFunctorialAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerCokernelToMultiplicativeGroupBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectingCocycleHypercohomologyLesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerConnectingUnitClassEqKummerClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerBoundaryLineBundleFirstChernClassStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem hk_pull_ext : ∀ (R : Type) [CommRing R] {K L : Cx R} (f : L ⟶ K) {F G : Shv R} {n : ℤ} (z : Cocycle (res R F) (res R G) n) (m k : ℤ) (h : m + n = k) (x : HK R K F m),
  HK.pull R f G k (HK.ext R K z m k h x) = HK.ext R L z m k h (HK.pull R f F m x) := by
  intro R _ K L f F G n z m k h x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem kummer_boundary : ∀ (q : ℕ) [NeZero q], ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) ∧ ∃ bd : ∀ (E : Spc) (n : ℤ), H ℤ E Gm n →+ Ht q E (n + 1) 1, (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → ∀ (n : ℤ) x, pull _ f _ _ (bd E' n x) = bd E n (pull _ f _ _ x)) ∧ (∀ (E : Spc), Inv q E → ∀ n : ℤ, Function.Exact (HK.post ℤ ((chains ℤ).obj E) ((q : ℤ) • 𝟙 Gm) n) (bd E n) ∧ Function.Exact (bd E n) (fun c => HK.post ℤ ((chains ℤ).obj E) κ (n + 1) (restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) c)) ∧ Function.Exact (fun c => HK.post ℤ ((chains ℤ).obj E) κ (n + 1) (restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) c)) (HK.post ℤ ((chains ℤ).obj E) ((q : ℤ) • 𝟙 Gm) (n + 1))) ∧ (∃ s : ℤˣ, ∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → bd (sch.obj X) 0 (secClass Gm (unitSec u)) = s • kum q u) ∧ ∃ s : ℤˣ, ∀ (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → bd E 1 (picClass L) = s • c1 q L := by
  intro q _
  obtain ⟨κ, hmono, h0, hgen, hker, hloc⟩ := GlobalTheory.T.kummer_sequence_etale_tateTwist q
  refine ⟨κ, hgen, ?_⟩
  let S : ShortComplex (Shv ℤ) := ShortComplex.mk κ (cokernel.π κ) (cokernel.condition κ)
  have hS : S.ShortExact :=
    { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel κ), mono_f := hmono, epi_g := (inferInstance : Epi (cokernel.π κ)) }
  obtain ⟨z, hex, s, hchar⟩ := GlobalTheory.T.exists_connecting_cocycle_hypercohomology_les ℤ S hS
  set qb := cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0 with hqb
  have hπq : cokernel.π κ ≫ qb = (q : ℤ) • 𝟙 Gm := cokernel.π_desc _ _ _
  have hbij := GlobalTheory.T.kummer_cokernel_to_multiplicativeGroup_bijective q κ h0 hker hloc
  have hP : ∀ E, Inv q E → ∀ n, Function.Bijective (HK.post ℤ ((chains ℤ).obj E) qb n) := fun E hE n =>
    GlobalTheory.T.etaleCohomology_bijective_of_support_bijective ℤ E qb (fun U hU => hbij U (hE U hU)) n
  have hR : ∀ E n, Function.Bijective (restrH (Int.castRingHom (ZMod q)) E (tw q 1) n) := fun E n =>
    GlobalTheory.T.etaleCohomology_coefficientRing_invariance ℤ (ZMod q) _ E (tw q 1) n
  have hpostc : ∀ (K : Cx ℤ) n x, HK.post ℤ K ((q : ℤ) • 𝟙 Gm) n x = HK.post ℤ K qb n (HK.post ℤ K (cokernel.π κ) n x) := by
    intro K n x
    rw [← hπq]
    exact (GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ K n).2.1 _ _ x
  let Pe : ∀ E, Inv q E → ∀ n, H ℤ E (cokernel κ) n ≃+ H ℤ E Gm n := fun E hE n =>
    AddEquiv.ofBijective (HK.post ℤ _ qb n) (hP E hE n)
  let Re : ∀ E n, Ht q E n 1 ≃+ H ℤ E ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) n := fun E n =>
    AddEquiv.ofBijective (restrH _ E (tw q 1) n) (hR E n)
  have hPe : ∀ E hE n x, Pe E hE n x = HK.post ℤ _ qb n x := fun _ _ _ _ => rfl
  have hRe : ∀ E n x, Re E n x = restrH _ E (tw q 1) n x := fun _ _ _ => rfl
  classical
  let bd : ∀ (E : Spc) (n : ℤ), H ℤ E Gm n →+ Ht q E (n + 1) 1 := fun E n =>
    if hE : Inv q E then
      (Re E (n + 1)).symm.toAddMonoidHom.comp ((HK.ext ℤ _ z n (n + 1) rfl).comp (Pe E hE n).symm.toAddMonoidHom)
    else 0
  have hbd : ∀ E (hE : Inv q E) n x, bd E n x = (Re E (n + 1)).symm (HK.ext ℤ _ z n (n + 1) rfl ((Pe E hE n).symm x)) := by
    intro E hE n x
    simp only [bd, dif_pos hE]
    rfl
  refine ⟨bd, ?_, ?_, ?_, ?_⟩
  · intro E E' f hE' n x
    have hE : Inv q E := fun U ⟨y⟩ => hE' U ⟨(f.app _).app _ y⟩
    rw [hbd E hE, hbd E' hE']
    apply (Re E (n + 1)).injective
    rw [AddEquiv.apply_symm_apply, hRe]
    have h1 : restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) (pull _ f _ _ ((Re E' (n + 1)).symm
        (HK.ext ℤ _ z n (n + 1) rfl ((Pe E' hE' n).symm x)))) =
        pull _ f _ _ (restrH (Int.castRingHom (ZMod q)) E' (tw q 1) (n + 1) ((Re E' (n + 1)).symm
        (HK.ext ℤ _ z n (n + 1) rfl ((Pe E' hE' n).symm x)))) :=
      ((restrMap (Int.castRingHom (ZMod q)) (tw q 1)).op.nat f (n + 1) _).symm
    rw [h1, ← hRe, AddEquiv.apply_symm_apply]
    have h2 : HK.pull ℤ ((chains ℤ).map f) (cokernel κ) n ((Pe E' hE' n).symm x) = (Pe E hE n).symm (pull _ f _ _ x) := by
      apply (Pe E hE n).injective
      rw [AddEquiv.apply_symm_apply, hPe E hE n]
      change HK.post ℤ _ qb n (HK.pull ℤ ((chains ℤ).map f) _ n _) = HK.pull ℤ ((chains ℤ).map f) _ n x
      rw [← (GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ _ n).2.2.2.2 ((chains ℤ).map f) qb, ← hPe E' hE', AddEquiv.apply_symm_apply]
    change HK.pull ℤ _ _ _ (HK.ext ℤ _ z n (n + 1) rfl _) = _
    rw [hk_pull_ext, h2]
  · intro E hE n
    obtain ⟨e1, e2, e3⟩ := hex ((chains ℤ).obj E) n
    obtain ⟨e1', -, -⟩ := hex ((chains ℤ).obj E) (n + 1)
    refine ⟨fun y => ?_, fun c => ?_, fun y => ?_⟩
    · rw [hbd E hE, AddEquivClass.map_eq_zero_iff, e2]
      constructor
      · rintro ⟨w, hw⟩
        refine ⟨w, ?_⟩
        rw [hpostc, ← hPe E hE, hw]
        exact AddEquiv.apply_symm_apply _ _
      · rintro ⟨w, rfl⟩
        refine ⟨w, ?_⟩
        change _ = (Pe E hE n).symm _
        rw [hpostc, ← hPe E hE, AddEquiv.symm_apply_apply]
    · change HK.post ℤ _ κ (n + 1) (restrH _ E (tw q 1) (n + 1) c) = 0 ↔ _
      rw [show HK.post ℤ _ κ (n + 1) = HK.post ℤ _ S.f (n + 1) from rfl, e3]
      constructor
      · rintro ⟨w, hw⟩
        refine ⟨(Pe E hE n) w, ?_⟩
        rw [hbd E hE, AddEquiv.symm_apply_apply]
        apply (Re E (n + 1)).injective
        rw [AddEquiv.apply_symm_apply, hw, hRe]
      · rintro ⟨w, rfl⟩
        refine ⟨(Pe E hE n).symm w, ?_⟩
        rw [hbd E hE, ← hRe, AddEquiv.apply_symm_apply]
    · rw [hpostc]
      have : HK.post ℤ _ qb (n + 1) (HK.post ℤ _ (cokernel.π κ) (n + 1) y) = 0 ↔ HK.post ℤ _ (cokernel.π κ) (n + 1) y = 0 := by
        rw [← hPe E hE]; exact (Pe E hE (n + 1)).map_eq_zero_iff
      rw [this, show HK.post ℤ _ (cokernel.π κ) (n + 1) = HK.post ℤ _ S.g (n + 1) from rfl, e1']
      constructor
      · rintro ⟨w, rfl⟩
        refine ⟨(Re E (n + 1)).symm w, ?_⟩
        change HK.post ℤ _ κ (n + 1) (Re E (n + 1) _) = _
        rw [AddEquiv.apply_symm_apply]
      · rintro ⟨c, rfl⟩
        exact ⟨_, rfl⟩
  · refine ⟨s, fun X u hu => ?_⟩
    have hE : Inv q (sch.obj X) := by
      rintro U ⟨x⟩
      have := hu.map x.appTop.hom
      rw [map_natCast] at this
      exact this
    obtain ⟨c, hc⟩ := (hbij X hu).2 (unitSec u)
    have hpre : (Pe _ hE 0).symm (secClass Gm (unitSec u)) = secClass (cokernel κ) c := by
      apply (Pe _ hE 0).injective
      rw [AddEquiv.apply_symm_apply, hPe _ hE 0, (GlobalTheory.T.degreeZeroSectionClass_properties ℤ (cokernel κ) X).2.2.2.2 qb c, hc]
    rw [hbd _ hE, hpre, GlobalTheory.T.kummerConnecting_unitClass_eq_kummerClass q κ h0 hmono hgen hker hloc hbij z s hchar X u c hu hc, Units.smul_def, Units.smul_def,
      map_zsmul, ← hRe, AddEquiv.symm_apply_apply]
  · refine ⟨s, fun E L hE => ?_⟩
    have hy : HK.post ℤ _ qb 1 ((Pe E hE 1).symm (picClass L)) = picClass L := by
      rw [← hPe E hE, AddEquiv.apply_symm_apply]
    rw [hbd E hE, GlobalTheory.T.kummerBoundary_lineBundle_firstChernClass q κ h0 hmono hgen hker hloc hbij z s hchar E L hE _ hy, Units.smul_def, Units.smul_def,
      map_zsmul, ← hRe, AddEquiv.symm_apply_apply]

end GlobalTheory
