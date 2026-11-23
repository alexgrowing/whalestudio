import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackCartierDivisorBundleEq
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem interNumRed_section : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ (y : Fin Y.dim → CartierDiv W.Z) (e : Fin Y.dim → Y.Dv), (∀ i, IsPull W.p₁ (y i) (e i) ∨ IsPull W.p₂ (y i) (e i)) → letI := algebraΓOfHom (W.p₁ ≫ Y.str); interNumRed F (⟨closure {W.δ (genericPoint Y.X)}, isClosed_closure⟩ : Closeds W.Z) (fun i => toLB (y i)) = Y.inter e := by
  intro F _ Y W y e h
  letI := algebraΓOfHom (W.p₁ ≫ Y.str)
  have hemb := W.δ.isClosedEmbedding
  have hcl : Set.range W.δ = closure {W.δ (genericPoint Y.X)} := by
    rw [← Set.image_singleton, hemb.closure_image_eq, genericPoint_spec Y.X, Set.image_univ]
  have hf : ∀ r : F, W.δ.appTop (algebraMap F Γ(W.Z, ⊤) r) = algebraMap F Γ(Y.X, ⊤) r := fun r => by
    show W.δ.appTop ((W.p₁ ≫ Y.str).appTop ((Scheme.ΓSpecIso (.of F)).inv r)) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Category.assoc, W.δ₁, Category.id_comp]
    rfl
  show interNumRed F _ _ = _
  rw [InterModel.interNumRed_eq_interNumOn F W.δ _ hcl, interNumOn_eq_interNum_pull hf fun i => isLB_toLB (y i)]
  refine (Var.inter_eq_of_toPic_eq (fun i => LB.isLB_pull (isLB_toLB (y i)) _) fun i => ?_).symm
  rw [cls_pull (isLB_toLB (y i)), toPic_apply]
  rcases h i with h | h
  · rw [← PullPres.pull_cls_toLB _ _ W.p₁ _ _ h, ← CechPic.pull_comp, W.δ₁, CechPic.pull_id]
  · rw [← PullPres.pull_cls_toLB _ _ W.p₂ _ _ h, ← CechPic.pull_comp, W.δ₂, CechPic.pull_id]

end GlobalTheory.FlagPush
