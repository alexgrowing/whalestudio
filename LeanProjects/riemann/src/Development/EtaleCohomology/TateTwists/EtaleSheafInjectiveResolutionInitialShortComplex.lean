import Development.EtaleCohomology.TateTwists.EtaleInjectiveResolutionSectionsLocallyExact

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ResSecPf

variable (R : Type) [CommRing R]

noncomputable abbrev secF (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)

example (U : Scheme.{0}) : PreservesLimits (secF R U) := inferInstance

lemma exact_pos (F : Shv R) (m n k : ℤ) (hn : 0 < n) (hm : m + 1 = n) (hk : n + 1 = k) :
    (ShortComplex.mk ((res R F).d m n) ((res R F).d n k) (by simp)).Exact := by
  have h1 : (res R F).ExactAt n := by
    unfold res
    rw [← quasiIsoAt_iff_exactAt (injectiveResolution F).ι' n
      (HomologicalComplex.exactAt_single_obj _ _ _ _ (by omega))]
    infer_instance
  exact (HomologicalComplex.exactAt_iff' _ m n k (by simp; omega) (by simp; omega)).1 h1

lemma subsing (F : Shv R) (U : Scheme.{0}) (n : ℤ) (hn : n < 0) :
    Subsingleton (Sec ((res R F).X n) U) := by
  have hz : IsZero ((res R F).X n) := by
    unfold res
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)
  have := (hz.of_iso (Iso.refl _)).eq_of_src (𝟙 _) 0
  constructor
  intro a b
  have e : ∀ x : Sec ((res R F).X n) U, x = 0 := by
    intro x
    have := congrArg (fun f => Sec.map f x) (hz.eq_of_src (𝟙 _) 0)
    simpa [Sec.map] using this
  rw [e a, e b]

lemma resι_e (F : Shv R) :
    resι R F ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom = (injectiveResolution F).ι.f 0 := by
  unfold resι
  rw [InjectiveResolution.ι'_f_zero]
  erw [Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

lemma d01' (F : Shv R) : ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom ≫
    (injectiveResolution F).cocomplex.d 0 1 = (injectiveResolution F).cochainComplex.d 0 1 ≫
      ((injectiveResolution F).cochainComplexXIso 1 1 rfl).hom := by
  rw [InjectiveResolution.cochainComplex_d _ 0 1 0 1 rfl rfl]
  simp

lemma etaleSheaf_injectiveResolution_initial_shortComplex_comp_zero (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  have h := (injectiveResolution F).ι'.comm 0 1
  unfold resι res
  refine (Category.assoc _ _ _).trans ?_
  erw [h]
  simp
  rfl

noncomputable abbrev S0 (F : Shv R) : ShortComplex (Shv R) := ShortComplex.mk _ _ (etaleSheaf_injectiveResolution_initial_shortComplex_comp_zero R F)

lemma etaleSheaf_injectiveResolution_initial_shortComplex_exact (F : Shv R) : (S0 R F).Exact := by
  let I := injectiveResolution F
  have hN : (ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d).Exact :=
    ShortComplex.exact_of_f_is_kernel _ I.isLimitKernelFork
  refine (ShortComplex.exact_iff_of_iso ?_).2 hN
  refine ShortComplex.isoMk (Iso.refl _) (I.cochainComplexXIso 0 0 rfl) (I.cochainComplexXIso 1 1 rfl) ?_ ?_
  · exact (Category.id_comp _).trans (resι_e R F).symm
  · exact d01' R F

lemma mono_resι_var (F : Shv R) : Mono (resι R F) := by
  have : Mono ((injectiveResolution F).ι.f 0) := inferInstance
  have h := resι_e R F
  have : Mono (resι R F ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom) := by
    rw [h]; assumption
  exact mono_of_mono _ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom

def exact_loc : Prop := ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact →
  ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b

lemma part1 (F : Shv R) (U : Scheme.{0}) (z : Sec ((res R F).X 0) U) :
    Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z := by
  constructor
  · intro hz
    have hE : ((S0 R F).map (secF R U)).Exact :=
      (etaleSheaf_injectiveResolution_initial_shortComplex_exact R F).map_of_mono_of_preservesKernel _ (mono_resι_var R F) inferInstance
    rw [ShortComplex.moduleCat_exact_iff] at hE
    exact hE z hz
  · rintro ⟨a, rfl⟩
    have := congrArg (fun f => Sec.map f a) (etaleSheaf_injectiveResolution_initial_shortComplex_comp_zero R F)
    simpa [Sec.map] using this

lemma part2 (F : Shv R) (U : Scheme.{0}) : Function.Injective (Sec.map (resι R F) (U := U)) := by
  have := mono_resι_var R F
  have : Mono ((secF R U).map (resι R F)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

end LateralTheory.EtaleFoundations.ResSecPf

open LateralTheory.EtaleFoundations.ResSecPf in
theorem LateralTheory.EtaleFoundations.etaleSheaf_injectiveResolution_sections_exact_of_local_exactness (hL : exact_loc) : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionSectionsLocallyExact := by
  intro R _ F U
  refine ⟨part1 R F U, part2 R F U, ?_, fun n hn => subsing R F U n hn⟩
  intro m n k hn hm z hk hz
  exact hL R _ (exact_pos R F m n k hn hm hk) U z hz
