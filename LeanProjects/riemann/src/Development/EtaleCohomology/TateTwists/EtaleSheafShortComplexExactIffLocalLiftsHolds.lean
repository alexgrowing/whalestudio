import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleSheafShortComplexExactIffLocallyLifts

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ExactIffPf

variable {R : Type} [CommRing R]

theorem inj_of_mono {F G : Shv R} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (Sec.map φ (U := U)) := by
  have : Mono φ.hom := inferInstance
  have : Mono (φ.hom.app (op U)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

theorem ker_sec {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) (b : Sec F U) (hb : Sec.map φ b = 0) :
    ∃ k : Sec (kernel φ) U, Sec.map (kernel.ι φ) k = b := by
  let E := sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙
    (evaluation _ _).obj (op U)
  have hl : IsLimit (Fork.ofι (E.map (kernel.ι φ))
      (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero, comp_zero]) :
      Fork (E.map φ) 0) := isLimitOfHasKernelOfPreservesLimit E φ
  let M := LinearMap.ker (φ.hom.app (op U)).hom
  let s : ModuleCat.of (ULift.{1} R) M ⟶ E.obj F := ModuleCat.ofHom M.subtype
  have hs : s ≫ E.map φ = s ≫ 0 := by
    ext x
    simp [s, E]
  obtain ⟨l, hl'⟩ := Fork.IsLimit.lift' hl s hs
  refine ⟨l.hom ⟨b, hb⟩, ?_⟩
  have := congrArg (fun m => m.hom (⟨b, hb⟩ : M)) hl'
  simpa [s, E] using this

theorem exact_iff (S : ShortComplex (Shv R)) : S.Exact ↔ ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 →
    Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b := by
  rw [S.exact_iff_epi_kernel_lift, ← Sheaf.isLocallySurjective_iff_epi' (φ := kernel.lift S.g S.f S.zero)]
  set φ := kernel.lift S.g S.f S.zero with hφ
  have hfac : ∀ V (a : Sec S.X₁ V), Sec.map (kernel.ι S.g) (Sec.map φ a) = Sec.map S.f a := by
    intro V a
    show ((φ ≫ kernel.ι S.g).hom.app (op V)).hom a = _
    rw [hφ, kernel.lift_ι]
  have hnat : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (k : Sec (kernel S.g) U),
      Sec.map (kernel.ι S.g) (Sec.res g k) = Sec.res g (Sec.map (kernel.ι S.g) k) := by
    intro V U g k
    have := congrArg (fun m => m.hom k) ((kernel.ι S.g).hom.naturality g.op)
    simp [Sec.map, Sec.res] at this ⊢
  constructor
  · intro h U b hb
    obtain ⟨k, rfl⟩ := ker_sec S.g U b hb
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} φ.hom k, ?_⟩
    rintro V g ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← hfac]
    rw [show Sec.map φ t = Sec.res g k from ht, hnat]
  · intro h
    constructor
    intro U k
    obtain ⟨T, hT, hTk⟩ := h U (Sec.map (kernel.ι S.g) k) (by
      show ((kernel.ι S.g ≫ S.g).hom.app (op U)).hom k = 0
      rw [kernel.condition]; rfl)
    refine Scheme.etaleTopology.superset_covering ?_ hT
    intro V g hg
    obtain ⟨a, ha⟩ := hTk V g hg
    refine ⟨a, ?_⟩
    apply inj_of_mono (kernel.ι S.g) V
    change Sec.map (kernel.ι S.g) (Sec.map φ a) = Sec.map (kernel.ι S.g) (Sec.res g k)
    rw [hfac, hnat, ha]

end LateralTheory.EtaleFoundations.ExactIffPf

theorem LateralTheory.EtaleFoundations.etale_sheaf_short_complex_exact_iff_local_lifts_holds : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts := by
  intro R _ S
  exact LateralTheory.EtaleFoundations.ExactIffPf.exact_iff S
