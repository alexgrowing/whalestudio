import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.KerSupp

theorem supportedIn_cokernel_kernelSubobject {X : Scheme.{0}} {F G : X.Modules} (g : F ⟶ G) {T : Set X}
    (h : Scheme.Modules.SupportedIn G T) :
    Scheme.Modules.SupportedIn (cokernel (kernelSubobject g).arrow) T := by
  let S : ShortComplex X.Modules := ShortComplex.mk (kernel.ι g) g (kernel.condition _)
  have hex : S.Exact := ShortComplex.exact_kernel _
  have hm : Mono (cokernel.desc S.f S.g S.zero) := S.exact_iff_mono_cokernel_desc.1 hex
  have h1 : Scheme.Modules.SupportedIn (cokernel (kernel.ι g)) T :=
    Scheme.Modules.SupportedIn.of_mono (cokernel.desc S.f S.g S.zero) h
  have e : (kernelSubobjectIso g).hom ≫ kernel.ι g = (kernelSubobject g).arrow :=
    kernelSubobject_arrow g
  let i : cokernel (kernelSubobject g).arrow ≅ cokernel (kernel.ι g) :=
    cokernelIsoOfEq e.symm ≪≫ (cokernelEpiComp (kernelSubobjectIso g).hom _)
  exact h1.of_iso i.symm

theorem toImage_surjective {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f] : Surjective f.toImage := by
  refine ⟨fun y => ?_⟩
  have h1 : f.imageι y ∈ (f.ker.support : Set X) := f.ker.range_subschemeι.le ⟨y, rfl⟩
  rw [Scheme.Hom.support_ker, f.isClosedMap.isClosed_range.closure_eq] at h1
  obtain ⟨x, hx⟩ := h1
  refine ⟨x, f.imageι.isEmbedding.injective ?_⟩
  rw [← hx, ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]

theorem isProper_image {S Y X : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [IsSeparated p]
    [LocallyOfFiniteType p] [QuasiCompact p] [IsProper f] (hY : IsProper (f ≫ p)) :
    IsProper (f.ker.subschemeι ≫ p) := by
  have := toImage_surjective f
  have hu : UniversallyClosed (f.toImage ≫ f.ker.subschemeι ≫ p) := by
    rw [← Category.assoc]
    change UniversallyClosed ((f.toImage ≫ f.imageι) ≫ p)
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  have : UniversallyClosed (f.ker.subschemeι ≫ p) := .of_comp_surjective f.toImage _
  exact ⟨⟩

theorem propSupp_adjKer {A : Type} [CommRing A] [IsNoetherianRing A] {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (φ : Z ⟶ X)
    (hφ : IsProper φ) (hc : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) {E : X.Modules}
    (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (hB : PropSupp A B) :
    PropSupp A (adjKer φ B) := by
  obtain ⟨TZ, hTZ, hsupp⟩ := hB
  let f : TZ.subscheme ⟶ X := TZ.subschemeι ≫ φ
  have hf : IsProper f := inferInstance
  have hfp : IsProper (f ≫ (X ↘ Spec (.of A))) := by
    change IsProper ((TZ.subschemeι ≫ φ) ≫ (X ↘ Spec (.of A)))
    rw [Category.assoc, hc]
    exact hTZ
  refine ⟨f.ker, isProper_image f _ hfp, ?_⟩
  have hpush := hsupp.pushforward φ
  have hsub : φ.base '' (TZ.support : Set Z) ⊆ (f.ker.support : Set X) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := TZ.range_subschemeι.ge hz
    rw [Scheme.Hom.support_ker]
    refine subset_closure ⟨w, ?_⟩
    rw [← hw]
    rfl
  exact supportedIn_cokernel_kernelSubobject (adjMap φ B) (hpush.mono hsub)

end GlobalTheory.CompanionTheory.GE.KerSupp
