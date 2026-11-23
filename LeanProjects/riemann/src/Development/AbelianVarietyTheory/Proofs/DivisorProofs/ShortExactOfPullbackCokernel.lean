import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitCokernelCoforkBiprodMap
open CategoryTheory Limits AlgebraicGeometry

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullbackSub

theorem shortExact_pullback_mono {C : Type*} [Category C] [Abelian C] {A E₂ E₃ F : C}
    (b : E₂ ⟶ E₃) (ι : F ⟶ E₃) [Epi b] [Mono ι]
    (f : A ⟶ E₂) (e : A ⟶ pullback b ι) [IsIso e] (hf : f = e ≫ pullback.fst b ι) :
    ∃ hz : f ≫ b ≫ cokernel.π ι = 0, (ShortComplex.mk f (b ≫ cokernel.π ι) hz).ShortExact := by
  subst hf
  have hz : (e ≫ pullback.fst b ι) ≫ b ≫ cokernel.π ι = 0 := by
    rw [Category.assoc, ← Category.assoc (pullback.fst b ι), pullback.condition, Category.assoc,
      cokernel.condition, comp_zero, comp_zero]
  refine ⟨hz, ?_⟩
  have hmf : Mono (e ≫ pullback.fst b ι) := inferInstance
  have hk := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel ι)
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ ?_) hmf
    (inferInstanceAs (Epi (b ≫ cokernel.π ι)))
  let ei : A ≅ pullback b ι := asIso e
  have hei : ei.hom = e := rfl
  have key : ∀ {T : C} (x : T ⟶ pullback b ι), (x ≫ ei.inv) ≫ e ≫ pullback.fst b ι = x ≫ pullback.fst b ι := by
    intro T x; rw [← hei, Category.assoc, Iso.inv_hom_id_assoc]
  refine KernelFork.IsLimit.ofι _ _
    (fun {T} g hg => pullback.lift g (KernelFork.IsLimit.lift' hk (g ≫ b)
        (by simpa [Category.assoc] using hg)).1
        (KernelFork.IsLimit.lift' hk (g ≫ b) (by simpa [Category.assoc] using hg)).2.symm ≫ ei.inv)
    (fun {T} g hg => ?_) (fun {T} g hg m hm => ?_)
  · exact (key _).trans (pullback.lift_fst _ _ _)
  · rw [← cancel_mono (e ≫ pullback.fst b ι)]
    exact hm.trans ((key _).trans (pullback.lift_fst _ _ _)).symm

theorem shortExact_preimage_of_epi_mono : ∀ (X : Scheme.{0}) {A E₂ E₃ F : X.Modules} (b : E₂ ⟶ E₃) (ι : F ⟶ E₃) [Epi b] [Mono ι]
    (f : A ⟶ E₂) (e : A ⟶ pullback b ι) [IsIso e], f = e ≫ pullback.fst b ι →
    ∃ hz : f ≫ b ≫ cokernel.π ι = 0, (ShortComplex.mk f (b ≫ cokernel.π ι) hz).ShortExact :=
  fun X _ _ _ _ b ι _ _ f e _ hf => shortExact_pullback_mono b ι f e hf

end GlobalTheory.PullbackSub
