import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocallyStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

abbrev secEvalFun (R : Type) [CommRing R] (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙ (evaluation _ _).obj (op U)

theorem injectiveResolution_sections_degree_zero_kernel (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) :
    (∀ w : Sec ((injectiveResolution F).cocomplex.X 0) U,
      Sec.map ((injectiveResolution F).cocomplex.d 0 1) w = 0 →
        ∃ a : Sec F U, Sec.map ((injectiveResolution F).ι.f 0) a = w) ∧
    Function.Injective (Sec.map ((injectiveResolution F).ι.f 0) (U := U)) := by
  set I := injectiveResolution F
  have hlim := KernelFork.mapIsLimit _ I.isLimitKernelFork (secEvalFun R U)
  let S : ShortComplex (ModuleCat.{1} (ULift.{1} R)) :=
    ShortComplex.mk ((secEvalFun R U).map (I.ι.f 0)) ((secEvalFun R U).map (I.cocomplex.d 0 1))
      (by rw [← Functor.map_comp, I.ι_f_zero_comp_complex_d, Functor.map_zero])
  have hS : S.Exact := S.exact_of_f_is_kernel hlim
  refine ⟨fun w hw => (ShortComplex.moduleCat_exact_iff S).1 hS w hw, ?_⟩
  have : Mono ((secEvalFun R U).map (I.ι.f 0)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

theorem chosenInjectiveResolutionAugmentation_eq_iota_comp (R : Type) [CommRing R] (F : Shv R) :
    resι R F = (injectiveResolution F).ι.f 0 ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).inv := by
  simp [resι, InjectiveResolution.ι'_f_zero]
  rfl

theorem chosenInjectiveResolutionEtaleSheaf_d_zero_one_eq (R : Type) [CommRing R] (F : Shv R) :
    (res R F).d 0 1 = ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom ≫
      (injectiveResolution F).cocomplex.d 0 1 ≫ ((injectiveResolution F).cochainComplexXIso 1 1 rfl).inv :=
  InjectiveResolution.cochainComplex_d _ 0 1 0 1 rfl rfl

theorem chosenInjectiveResolutionEtaleSheaf_exactAt_ne_zero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n ≠ 0) : (res R F).ExactAt n := by
  have h : ((CochainComplex.singleFunctor (Shv R) 0).obj F).ExactAt n :=
    HomologicalComplex.exactAt_single_obj (ComplexShape.up ℤ) 0 F n hn
  exact (quasiIsoAt_iff_exactAt (injectiveResolution F).ι' n h).1 inferInstance

theorem resSec (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) :
    (∀ z : Sec ((res R F).X 0) U, Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z) ∧
    Function.Injective (Sec.map (resι R F) (U := U)) ∧
    (∀ (m n k : ℤ), 0 < n → m + 1 = n → ∀ z : Sec ((res R F).X n) U, n + 1 = k →
      Sec.map ((res R F).d n k) z = 0 →
        Loc U fun V g => ∃ y : Sec ((res R F).X m) V, Sec.map ((res R F).d m n) y = Sec.res g z) ∧
    ∀ n : ℤ, n < 0 → Subsingleton (Sec ((res R F).X n) U) := by
  obtain ⟨hker, hinj⟩ := injectiveResolution_sections_degree_zero_kernel R F U
  set I := injectiveResolution F
  set e0 := I.cochainComplexXIso 0 0 rfl
  set e1 := I.cochainComplexXIso 1 1 rfl
  have hι : ∀ a : Sec F U, Sec.map (resι R F) a = Sec.map e0.inv (Sec.map (I.ι.f 0) a) := by
    intro a; rw [chosenInjectiveResolutionAugmentation_eq_iota_comp]; rfl
  have hd : ∀ z : Sec ((res R F).X 0) U,
      Sec.map ((res R F).d 0 1) z = Sec.map e1.inv (Sec.map (I.cocomplex.d 0 1) (Sec.map e0.hom z)) := by
    intro z; rw [chosenInjectiveResolutionEtaleSheaf_d_zero_one_eq]; rfl
  have he0 : ∀ z : Sec ((res R F).X 0) U, Sec.map e0.inv (Sec.map e0.hom z) = z := by
    intro z; change Sec.map (e0.hom ≫ e0.inv) z = z; rw [e0.hom_inv_id]; rfl
  have he0' : ∀ w : Sec (I.cocomplex.X 0) U, Sec.map e0.hom (Sec.map e0.inv w) = w := by
    intro w; change Sec.map (e0.inv ≫ e0.hom) w = w; rw [e0.inv_hom_id]; rfl
  have he1 : ∀ w : Sec (I.cocomplex.X 1) U, Sec.map e1.hom (Sec.map e1.inv w) = w := by
    intro w; change Sec.map (e1.inv ≫ e1.hom) w = w; rw [e1.inv_hom_id]; rfl
  refine ⟨fun z => ⟨fun hz => ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hd] at hz
    have hz' : Sec.map (I.cocomplex.d 0 1) (Sec.map e0.hom z) = 0 := by
      have := congrArg (Sec.map e1.hom) hz
      rw [he1] at this
      exact this.trans (map_zero (e1.hom.hom.app (op U)).hom)
    obtain ⟨a, ha⟩ := hker _ hz'
    exact ⟨a, by rw [hι, ha, he0]⟩
  · rintro ⟨a, rfl⟩
    rw [hd, hι, he0']
    change Sec.map e1.inv (Sec.map (I.ι.f 0 ≫ I.cocomplex.d 0 1) a) = 0
    rw [I.ι_f_zero_comp_complex_d]
    exact map_zero _
  · intro a b hab
    rw [hι, hι] at hab
    have := congrArg (Sec.map e0.hom) hab
    rw [he0', he0'] at this
    exact hinj this
  · intro m n k hn hmn z hnk hz
    have hex : ((res R F).sc' m n k).Exact :=
      (HomologicalComplex.exactAt_iff' _ m n k (by simp; omega) (by simp; omega)).1
        (chosenInjectiveResolutionEtaleSheaf_exactAt_ne_zero R F n (by omega))
    exact (GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally R ((res R F).sc' m n k)).1 hex U z hz
  · intro n hn
    haveI : (res R F).IsStrictlyGE 0 := (inferInstance : I.cochainComplex.IsStrictlyGE 0)
    have h0 : IsZero ((res R F).X n) := CochainComplex.isZero_of_isStrictlyGE _ 0 n hn
    exact ModuleCat.isZero_iff_subsingleton.1 ((secEvalFun R U).map_isZero h0)

end GlobalTheory.EtC
